import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Pullbacks
import PrimalitySheafVerification.ManuscriptAudit.FlatDiagonalResidueField

/-! Each point of a weakly étale scheme over an algebraically closed
field is the image of a rational section of the structure map. -/

namespace ManuscriptAudit.WeaklyEtaleAlgebraicallyClosed

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

private theorem fromSpecStalk_flat (X : Scheme.{u}) (x : X) : Flat (X.fromSpecStalk x) := by
  let a := X.affineCover.f (X.affineCover.idx x)
  let U := a.opensRange
  let hU : IsAffineOpen U := isAffineOpen_opensRange a
  let hx : x ∈ U := X.affineCover.covers x
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hx, IsAffineOpen.fromSpecStalk]
  letI : Flat (Spec.map (X.presheaf.germ U x hx)) := by
    apply Flat.SpecMap_iff.mpr
    letI : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
    letI := hU.isLocalization_stalk ⟨x, hx⟩
    exact IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  infer_instance

/-- The native map from the spectrum of a local ring to its scheme is
weakly étale: it is a flat monomorphism. -/
theorem fromSpecStalk_weaklyEtale (X : Scheme.{u}) (x : X) : WeaklyEtale (X.fromSpecStalk x) := by
  letI : Flat (X.fromSpecStalk x) := fromSpecStalk_flat X x
  exact ⟨inferInstance, inferInstance⟩

private theorem flatTensorMultiplication (K B : Type u) [Field K] [CommRing B] [Algebra K B]
    [WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap K B)))] :
    (Algebra.TensorProduct.lmul' (S := B) K).Flat := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap K B))
  let e := AlgebraicGeometry.pullbackSpecIso K B B
  have h : Flat (pullback.diagonal g ≫ e.hom) := inferInstance
  apply Flat.SpecMap_iff.mp
  simpa only [g, e, AlgebraicGeometry.diagonal_SpecMap, Category.assoc, Iso.inv_hom_id, Category.comp_id] using h

/-- Every point of a weakly étale scheme over an algebraically closed
field gives an actual rational section through that point. -/
theorem rationalSectionThrough (K : Type u) [Field K] [IsAlgClosed K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) [WeaklyEtale f] (x : X) :
    ∃ s : Spec (CommRingCat.of K) ⟶ X,
      s ≫ f = 𝟙 _ ∧ s (IsLocalRing.closedPoint K) = x := by
  let B := X.presheaf.stalk x
  letI : IsLocalRing B := inferInstance
  letI : WeaklyEtale (X.fromSpecStalk x) := fromSpecStalk_weaklyEtale X x
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.fromSpecStalk x ≫ f)
  letI : Algebra K B := φ.hom.toAlgebra
  have hflat : WeaklyEtale (X.fromSpecStalk x ≫ f) := inferInstance
  rw [← hφ] at hflat
  letI : WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap K B))) := hflat
  let e := FlatDiagonalResidueField.residueFieldEquiv K B (flatTensorMultiplication K B)
  let i : X.residueField x ⟶ CommRingCat.of K := CommRingCat.ofHom e.symm.toRingHom
  refine ⟨Spec.map i ≫ X.fromSpecResidueField x, ?_, ?_⟩
  · simp only [Scheme.fromSpecResidueField, Category.assoc, ← hφ, ← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext a
    exact e.symm_apply_apply a
  · simp only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

end
end ManuscriptAudit.WeaklyEtaleAlgebraicallyClosed

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeaklyEtaleAlgebraicallyClosed.fromSpecStalk_weaklyEtale,
      ``ManuscriptAudit.WeaklyEtaleAlgebraicallyClosed.rationalSectionThrough] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
