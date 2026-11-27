import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.Algebra.CharP.Defs
import PrimalitySheafVerification.ManuscriptAudit.NodalProjectiveClosure

/-! The characteristic-two coordinate translation is a genuine
involution of the standard projective plane, fixing the (Z)-chart. -/

namespace ManuscriptAudit.NodalCharacteristicTwoPlane

open AlgebraicGeometry CategoryTheory Graded
open CuspProperCompactification (projectivePlane standardPlaneGrading standardPlane_X_mem_one)
open HomogeneousIdeal

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

universe u
variable (K : Type u) [Field K] [CharP K 2]

abbrev P := MvPolynomial (Fin 3) K
private abbrev G := standardPlaneGrading K
private abbrev X (i : Fin 3) : P K := MvPolynomial.X i

private theorem two_eq_zero : (2 : P K) = 0 := by
  simpa only [map_ofNat, map_zero] using
    congrArg MvPolynomial.C (CharP.ofNat_eq_zero K 2)

def chartValues (i : Fin 3) : P K :=
  if i = 1 then X K 1 + X K 0 else X K i

def coordinateChange : P K →ₐ[K] P K := MvPolynomial.aeval (chartValues K)

@[simp] theorem coordinateChange_X0 : coordinateChange K (X K 0) = X K 0 := by
  simp [coordinateChange, chartValues]

@[simp] theorem coordinateChange_X1 : coordinateChange K (X K 1) = X K 1 + X K 0 := by
  simp [coordinateChange, chartValues]

@[simp] theorem coordinateChange_X2 : coordinateChange K (X K 2) = X K 2 := by
  simp [coordinateChange, chartValues]

private theorem coordinateChange_involutive : Function.Involutive (coordinateChange K) := by
  have h : (coordinateChange K).comp (coordinateChange K) = AlgHom.id K (P K) := by
    apply MvPolynomial.algHom_ext
    intro i
    change coordinateChange K (coordinateChange K (X K i)) = X K i
    have hAdd : X K 0 + X K 0 = 0 := by rw [← two_mul, two_eq_zero K, zero_mul]
    fin_cases i <;>
      simp only [coordinateChange_X0, coordinateChange_X1, coordinateChange_X2,
        map_add, add_assoc, hAdd, add_zero]
  intro a
  exact DFunLike.congr_fun h a

def gradedChange : G K →+*ᵍ G K where
  toRingHom := (coordinateChange K).toRingHom
  map_mem := by
    intro n a ha
    change a.IsHomogeneous n at ha
    change (coordinateChange K a).IsHomogeneous n
    have hValues (i : Fin 3) : (chartValues K i).IsHomogeneous 1 := by
      unfold chartValues
      split
      · exact (MvPolynomial.isHomogeneous_X K _).add (MvPolynomial.isHomogeneous_X K _)
      · exact MvPolynomial.isHomogeneous_X K _
    simpa only [coordinateChange, one_mul] using ha.aeval (chartValues K) hValues

private theorem gradedChange_comp :
    (gradedChange K).comp (gradedChange K) = GradedRingHom.id (G K) := by
  apply GradedRingHom.ext
  exact coordinateChange_involutive K

theorem irrelevant_le_map :
    (G K)₊ ≤ (G K)₊.map (gradedChange K) := by
  apply (HomogeneousIdeal.irrelevant_le _).mpr
  intro i hi a ha
  have ha' : gradedChange K a ∈ (G K)₊ :=
    HomogeneousIdeal.mem_irrelevant_of_mem _ hi ((gradedChange K).map_mem ha)
  have he : gradedChange K (gradedChange K a) = a :=
    coordinateChange_involutive K a
  exact he ▸ Ideal.mem_map_of_mem (gradedChange K).toRingHom ha'

def planeChange : projectivePlane K ⟶ projectivePlane K :=
  Proj.map (gradedChange K) (irrelevant_le_map K)

theorem planeChange_comp : planeChange K ≫ planeChange K = 𝟙 _ := by
  have map_eq_id (f : G K →+*ᵍ G K) (hf : (G K)₊ ≤ (G K)₊.map f)
      (h : f = GradedRingHom.id (G K)) : Proj.map f hf = 𝟙 _ := by
    subst f
    exact Proj.map_id
  rw [planeChange, ← Proj.map_comp]
  exact map_eq_id _ _ (gradedChange_comp K)

/-- The coordinate involution is an isomorphism of the projective plane. -/
def planeIso : projectivePlane K ≅ projectivePlane K where
  hom := planeChange K
  inv := planeChange K
  hom_inv_id := planeChange_comp K
  inv_hom_id := planeChange_comp K

/-- The homogeneous node equation is sent to the cusp equation in
characteristic two by the same native coordinate change. -/
theorem homogeneousEquation_change :
    coordinateChange K (NodalProjectiveClosure.homogeneousEquation K) =
      CuspProperCompactification.planeCubic K := by
  change coordinateChange K (X K 1 ^ 2 * X K 2 - X K 0 ^ 2 * (X K 0 + X K 2)) =
    X K 1 ^ 2 * X K 2 - X K 0 ^ 3
  rw [map_sub, map_mul, map_pow, map_mul, map_pow, map_add,
    coordinateChange_X0, coordinateChange_X1, coordinateChange_X2]
  have hSq : (X K 1 + X K 0) ^ 2 = X K 1 ^ 2 + X K 0 ^ 2 := by
    calc
      _ = X K 1 ^ 2 + (2 : P K) * X K 1 * X K 0 + X K 0 ^ 2 := by ring
      _ = _ := by rw [two_eq_zero K, zero_mul, zero_mul, add_zero]
  rw [hSq]
  ring

end
end ManuscriptAudit.NodalCharacteristicTwoPlane

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalCharacteristicTwoPlane.planeChange_comp,
      ``ManuscriptAudit.NodalCharacteristicTwoPlane.planeIso,
      ``ManuscriptAudit.NodalCharacteristicTwoPlane.homogeneousEquation_change] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
