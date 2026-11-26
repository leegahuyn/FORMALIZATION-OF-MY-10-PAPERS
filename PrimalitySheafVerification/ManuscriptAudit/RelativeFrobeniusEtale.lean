import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import PrimalitySheafVerification.ManuscriptAudit.AffineRelativeFrobenius

/-!
# Étaleness of relative Frobenius for an étale algebra

The right inclusion into the Frobenius base change is étale by base
change. Composing it with relative Frobenius gives the original
algebra map, with its source identified with the twisted copy.
-/

namespace ManuscriptAudit.RelativeFrobeniusEtale

open AlgebraicGeometry CategoryTheory ManuscriptAudit.AffineRelativeFrobenius
open scoped TensorProduct

universe u

noncomputable section

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable (p : ℕ) [Fact p.Prime] [CharP A p] [CharP B p]

/-- The right inclusion into the Frobenius base change, sending `a` to `1 ⊗ a`. -/
def rightInclusion : FrobeniusTwist p A →+* (B ⊗[A] FrobeniusTwist p A) :=
  (Algebra.TensorProduct.includeRight :
    FrobeniusTwist p A →ₐ[A] B ⊗[A] FrobeniusTwist p A).toRingHom

/-- The original algebra map, with the source viewed as the twisted copy. -/
def twistedStructureMap : FrobeniusTwist p A →+* B :=
  algebraMap A B

theorem relativeFrobenius_comp_rightInclusion :
    (relativeFrobenius A B p).comp (rightInclusion A B p) = twistedStructureMap A B p := by
  apply RingHom.ext
  intro a
  change relativeFrobenius A B p ((1 : B) ⊗ₜ[A] a) = algebraMap A B (show A from a)
  rw [relativeFrobenius_tmul, one_pow, one_mul]

/-- The Frobenius base change is étale over the right factor. -/
theorem rightInclusion_etale [Algebra.Etale A B] : (rightInclusion A B p).Etale := by
  letI : Algebra (FrobeniusTwist p A) (B ⊗[A] FrobeniusTwist p A) :=
    Algebra.TensorProduct.rightAlgebra
  change (algebraMap (FrobeniusTwist p A) (B ⊗[A] FrobeniusTwist p A)).Etale
  apply RingHom.etale_algebraMap.mpr
  exact Algebra.Etale.of_equiv (Algebra.TensorProduct.commRight A (FrobeniusTwist p A) B)

/-- The actual morphism on spectra induced by relative Frobenius is étale. -/
theorem spec_relativeFrobenius_etale [Algebra.Etale A B] :
    Etale (Spec.map (CommRingCat.ofHom (relativeFrobenius A B p))) := by
  let i := CommRingCat.ofHom (rightInclusion A B p)
  let f := CommRingCat.ofHom (relativeFrobenius A B p)
  let g := CommRingCat.ofHom (twistedStructureMap A B p)
  have hi : Etale (Spec.map i) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (rightInclusion_etale A B p)
  have hg : Etale (Spec.map g) := by
    apply (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    change (algebraMap A B).Etale
    exact RingHom.etale_algebraMap.mpr inferInstance
  have hRing : i ≫ f = g :=
    CommRingCat.hom_ext (relativeFrobenius_comp_rightInclusion A B p)
  have hScheme : Spec.map f ≫ Spec.map i = Spec.map g := by
    rw [← Spec.map_comp, hRing]
  letI : Etale (Spec.map i) := hi
  letI : Etale (Spec.map f ≫ Spec.map i) := hScheme.symm ▸ hg
  exact Etale.of_comp (Spec.map f) (Spec.map i)

end

end ManuscriptAudit.RelativeFrobeniusEtale

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.RelativeFrobeniusEtale.relativeFrobenius_comp_rightInclusion,
      ``ManuscriptAudit.RelativeFrobeniusEtale.rightInclusion_etale,
      ``ManuscriptAudit.RelativeFrobeniusEtale.spec_relativeFrobenius_etale] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
