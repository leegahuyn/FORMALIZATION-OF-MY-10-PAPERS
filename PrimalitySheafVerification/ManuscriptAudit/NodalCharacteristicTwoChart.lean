import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalCharacteristicTwoPlane
import PrimalitySheafVerification.ManuscriptAudit.NodalCharacteristicTwoAffine

/-! The vertical change on the affine coordinate rings agrees with
the graded change on the actual projective (Z)-chart. -/

namespace ManuscriptAudit.NodalCharacteristicTwoChart

open AlgebraicGeometry CategoryTheory HomogeneousLocalization Graded
open CuspProperCompactification (standardZChartRing standardPlaneGrading standardPlane_X_mem_one
  standardZChartEvaluation_mk affineZChartι affineChartEvaluation
  affineChartEvaluation_mk_coe cuspInPlane cuspInPlane_as_Z_chart)
open NodalCharacteristicTwoPlane (coordinateChange chartValues gradedChange irrelevant_le_map planeChange)
open NodalCharacteristicTwoAffine (coordinateEquiv coordinateEquiv_x coordinateEquiv_y cuspCube affineIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
variable (K : Type u) [Field K] [CharP K 2]

private abbrev P := MvPolynomial (Fin 3) K
private abbrev G := standardPlaneGrading K
private abbrev z : P K := MvPolynomial.X (2 : Fin 3)
private abbrev node := NodalConductor.coordinates K
private abbrev cusp := CuspPunctured.CuspSubalgebra K

private def awayMapAt {v w : P K} (h : gradedChange K v = w) :
    Away (G K) v →+* Away (G K) w := by
  subst w
  exact Away.map (gradedChange K) v

private theorem awayMapAt_mk {v w : P K} (h : gradedChange K v = w)
    (hv : v ∈ G K 1) (hw : w ∈ G K 1) (n : ℕ) (p : P K) (hp : p ∈ G K (n • 1)) :
    awayMapAt K h (Away.mk (G K) hv n p hp) =
      Away.mk (G K) hw n (gradedChange K p) ((gradedChange K).map_mem hp) := by
  subst w
  exact Away.map_mk (gradedChange K) v hv n p hp

private theorem awayι_map_at {v w : P K} (h : gradedChange K v = w)
    (hv : v ∈ G K 1) (hw : w ∈ G K 1) :
    Proj.awayι (G K) w hw (by decide) ≫ planeChange K =
      Spec.map (CommRingCat.ofHom (awayMapAt K h)) ≫ Proj.awayι (G K) v hv (by decide) := by
  subst w
  exact Proj.awayι_comp_map (gradedChange K) (irrelevant_le_map K) (by decide) v hv

private theorem z_fixed : gradedChange K (z K) = z K :=
  NodalCharacteristicTwoPlane.coordinateChange_X2 K

def zChartChange : standardZChartRing K →+* standardZChartRing K :=
  awayMapAt K (z_fixed K)

private theorem zChartChange_mk (n : ℕ) (p : P K) (hp : p ∈ G K (n • 1)) :
    zChartChange K (Away.mk (G K) (standardPlane_X_mem_one K 2) n p hp) =
      Away.mk (G K) (standardPlane_X_mem_one K 2) n (gradedChange K p)
        ((gradedChange K).map_mem hp) :=
  awayMapAt_mk K (z_fixed K) (standardPlane_X_mem_one K 2)
    (standardPlane_X_mem_one K 2) n p hp

private theorem z_chart_comm :
    affineZChartι K ≫ planeChange K = Spec.map (CommRingCat.ofHom (zChartChange K)) ≫
      affineZChartι K :=
  awayι_map_at K (z_fixed K) (standardPlane_X_mem_one K 2) (standardPlane_X_mem_one K 2)

private def cuspValues (i : Fin 3) : Polynomial K :=
  if i = 0 then (Polynomial.X : Polynomial K) ^ 2
  else if i = 1 then Polynomial.X ^ 3 else 1

private theorem eval_coordinateChange (p : P K) :
    ((cusp K).val.comp (((coordinateEquiv K).toAlgHom).comp
      (MvPolynomial.aeval (NodalProjectiveClosure.chartValues K)))) p =
    ((MvPolynomial.aeval (cuspValues K)).comp (coordinateChange K)) p := by
  have h : (cusp K).val.comp (((coordinateEquiv K).toAlgHom).comp
      (MvPolynomial.aeval (NodalProjectiveClosure.chartValues K))) =
    (MvPolynomial.aeval (cuspValues K)).comp (coordinateChange K) := by
    apply MvPolynomial.algHom_ext
    intro i
    change ((coordinateEquiv K ((MvPolynomial.aeval (NodalProjectiveClosure.chartValues K))
      (MvPolynomial.X i)) : cusp K) : Polynomial K) =
      (MvPolynomial.aeval (cuspValues K)) (coordinateChange K (MvPolynomial.X i))
    rw [MvPolynomial.aeval_X]
    fin_cases i
    · change ((coordinateEquiv K (NodalAffinePresentation.nodeX K) : cusp K) : Polynomial K) =
        (MvPolynomial.aeval (cuspValues K)) (coordinateChange K (MvPolynomial.X (0 : Fin 3)))
      rw [coordinateEquiv_x K, NodalCharacteristicTwoPlane.coordinateChange_X0,
        MvPolynomial.aeval_X] <;> rfl
    · change ((coordinateEquiv K (NodalAffinePresentation.nodeY K) : cusp K) : Polynomial K) =
        (MvPolynomial.aeval (cuspValues K)) (coordinateChange K (MvPolynomial.X (1 : Fin 3)))
      rw [coordinateEquiv_y K, NodalCharacteristicTwoPlane.coordinateChange_X1,
        map_add, MvPolynomial.aeval_X, MvPolynomial.aeval_X] <;> rfl
    · change ((coordinateEquiv K 1 : cusp K) : Polynomial K) =
        (MvPolynomial.aeval (cuspValues K)) (coordinateChange K (MvPolynomial.X (2 : Fin 3)))
      rw [map_one, NodalCharacteristicTwoPlane.coordinateChange_X2, MvPolynomial.aeval_X] <;> rfl
  exact DFunLike.congr_fun h p

theorem zChart_eval_comm :
    (coordinateEquiv K).toRingHom.comp (NodalProjectiveClosure.chartEvaluation K) =
      (affineChartEvaluation K).comp (zChartChange K) := by
  apply RingHom.ext
  intro a
  obtain ⟨n, p, hp, rfl⟩ := Away.mk_surjective (G K) (standardPlane_X_mem_one K 2) a
  apply Subtype.ext
  change ((coordinateEquiv K (NodalProjectiveClosure.chartEvaluation K
    (Away.mk (G K) (standardPlane_X_mem_one K 2) n p hp)) : cusp K) : Polynomial K) =
    ((affineChartEvaluation K (zChartChange K
    (Away.mk (G K) (standardPlane_X_mem_one K 2) n p hp))) : Polynomial K)
  unfold NodalProjectiveClosure.chartEvaluation
  rw [standardZChartEvaluation_mk, zChartChange_mk]
  have h_eval := affineChartEvaluation_mk_coe K n (gradedChange K p)
    ((gradedChange K).map_mem hp)
  rw [h_eval]
  exact eval_coordinateChange K p

/-- The actual two affine embeddings into the projective plane commute
with their characteristic-two coordinate isomorphisms. -/
theorem affine_square :
    (affineIso K).hom ≫ NodalProjectiveClosure.nodeInPlane K =
      cuspInPlane K ≫ planeChange K := by
  unfold NodalProjectiveClosure.nodeInPlane
  rw [cuspInPlane_as_Z_chart, Category.assoc, z_chart_comm]
  change Spec.map (CommRingCat.ofHom (coordinateEquiv K).toRingHom) ≫
      (Spec.map (CommRingCat.ofHom (NodalProjectiveClosure.chartEvaluation K)) ≫ affineZChartι K) =
    Spec.map (CommRingCat.ofHom (affineChartEvaluation K)) ≫
      (Spec.map (CommRingCat.ofHom (zChartChange K)) ≫ affineZChartι K)
  rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  apply congrArg (fun a : CommRingCat.of (standardZChartRing K) ⟶ CommRingCat.of (cusp K) =>
    Spec.map a ≫ affineZChartι K)
  apply CommRingCat.hom_ext
  exact zChart_eval_comm K

end
end ManuscriptAudit.NodalCharacteristicTwoChart

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalCharacteristicTwoChart.zChart_eval_comm,
      ``ManuscriptAudit.NodalCharacteristicTwoChart.affine_square] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
