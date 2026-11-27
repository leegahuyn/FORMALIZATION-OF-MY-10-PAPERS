import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspProperCompactification

/-! The structure map of the existing projective plane on any of its
native standard affine charts. -/

namespace ManuscriptAudit.NodalPlaneChartBase

open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open CuspProperCompactification
  (projectivePlane projectivePlaneToBase standardPlaneGrading standardPlane_X_mem_one)

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (K : Type u) [Field K]

private abbrev D := standardPlaneGrading K

private lemma constant_mem_zero (a : K) :
    (MvPolynomial.C a : MvPolynomial (Fin 3) K) ∈ D K 0 :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_C _ _)

private def constants : K →+* D K 0 where
  toFun a := ⟨MvPolynomial.C a, constant_mem_zero K a⟩
  map_one' := Subtype.ext (map_one MvPolynomial.C)
  map_mul' a b := Subtype.ext (map_mul MvPolynomial.C a b)
  map_zero' := Subtype.ext (map_zero MvPolynomial.C)
  map_add' a b := Subtype.ext (map_add MvPolynomial.C a b)

private theorem planeToBase_eq :
    projectivePlaneToBase K =
      Proj.toSpecZero (D K) ≫ Spec.map (CommRingCat.ofHom (constants K)) := rfl

/-- Standard affine chart morphisms preserve the structure map to the field
when their constant coordinates are preserved. -/
theorem standardPlaneChartPoint_toBase {R : Type u} [CommRing R] [Algebra K R]
    (i : Fin 3)
    (e : Away (D K) (MvPolynomial.X i) →+* R)
    (h : ∀ a : K, e (Away.mk (D K) (standardPlane_X_mem_one K i) 0 (MvPolynomial.C a)
      (by simpa only [zero_nsmul] using constant_mem_zero K a)) = algebraMap K R a) :
    Spec.map (CommRingCat.ofHom e) ≫
      Proj.awayι (D K) (MvPolynomial.X i) (standardPlane_X_mem_one K i) (by decide) ≫
      projectivePlaneToBase K =
      Spec.map (CommRingCat.ofHom (algebraMap K R)) := by
  rw [planeToBase_eq]
  simp only [Category.assoc, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change e (fromZeroRingHom (D K) _ (constants K a)) = _
  change e (Away.mk (D K) (standardPlane_X_mem_one K i) 0 (MvPolynomial.C a)
    (by simpa only [zero_nsmul] using constant_mem_zero K a)) = _
  exact h a

end
end ManuscriptAudit.NodalPlaneChartBase

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NodalPlaneChartBase.standardPlaneChartPoint_toBase
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
