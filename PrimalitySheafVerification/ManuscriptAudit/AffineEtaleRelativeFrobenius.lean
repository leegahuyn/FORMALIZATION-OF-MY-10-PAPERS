import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineFrobeniusFactorization
import PrimalitySheafVerification.ManuscriptAudit.EtaleRadicial
import PrimalitySheafVerification.ManuscriptAudit.RelativeFrobeniusEtale

/-!
# Relative Frobenius is an isomorphism for an affine étale algebra

For an étale algebra the relative Frobenius map is itself étale. Its two
composites with the left inclusion act as absolute Frobenius, so the
actual map of affine schemes is surjective and universally injective.
-/

namespace ManuscriptAudit.AffineEtaleRelativeFrobenius

open AlgebraicGeometry CategoryTheory
open AffineRelativeFrobenius AffineFrobeniusFactorization
open scoped TensorProduct

noncomputable section

universe u

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable (p : ℕ) [Fact p.Prime] [CharP A p] [CharP B p]

/-- The relative Frobenius of the actual affine étale algebra is an
isomorphism on spectra. -/
theorem spec_relativeFrobenius_isIso [Algebra.Etale A B] :
    IsIso (Spec.map (CommRingCat.ofHom (relativeFrobenius A B p))) := by
  let f := relativeFrobenius A B p
  let g := leftInclusion A B p
  have hSource (z : B ⊗[A] FrobeniusTwist p A) : g (f z) = z ^ p :=
    (pow_eq_leftInclusion_relativeFrobenius A B p z).symm
  have hTarget (b : B) : f (g b) = b ^ p :=
    DFunLike.congr_fun (relativeFrobenius_comp_leftInclusion A B p) b
  letI : Etale (specMap f) := RelativeFrobeniusEtale.spec_relativeFrobenius_etale A B p
  letI : Surjective (specMap f) := specMap_surjective_of_factors_power f p g hSource
  letI : UniversallyInjective (specMap f) :=
    specMap_universallyInjective_of_power_lifts f p (CharP.cast_eq_zero B p)
      (fun b => ⟨g b, hTarget b⟩)
  exact EtaleRadicial.isIso_of_etale_of_surjective_of_universallyInjective (specMap f)

end

end ManuscriptAudit.AffineEtaleRelativeFrobenius

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.AffineEtaleRelativeFrobenius.spec_relativeFrobenius_isIso
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
