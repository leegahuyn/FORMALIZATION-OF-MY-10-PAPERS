import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CyclicPowerInverseLimit
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleCoefficientReduction

/-! Ordinary inverse limits of the actual prime-power cohomology of an open immersion. -/

namespace ManuscriptAudit.OpenEtaleCyclicInverseLimit

open AlgebraicGeometry CategoryTheory
open OpenComplementRationalPointCohomology (extensionH)
open OpenEtaleCoefficientReduction (reductionH)

noncomputable section

set_option backward.isDefEq.respectTransparency false
attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]
variable (ℓ : ℕ) [Fact ℓ.Prime]

local instance prime_neZero : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
local instance power_neZero (r : ℕ) : NeZero (ℓ ^ r) :=
  ⟨pow_ne_zero r (Fact.out : ℓ.Prime).ne_zero⟩

private abbrev cohomology (d n : ℕ) := extensionH j (AddCommGrpCat.of (ZMod d)) n

private def orderCongr {a b : ℕ} (h : a = b) (n : ℕ) :
    cohomology j a n ≃+ cohomology j b n := by
  subst b
  exact AddEquiv.refl _

/-- The actual coefficient transition, with the source order identified as the next power. -/
def transition (n r : ℕ) :
    cohomology j (ℓ ^ (r + 1)) n →+ cohomology j (ℓ ^ r) n :=
  (reductionH j (ℓ ^ r) ℓ n).comp (orderCongr j (pow_succ ℓ r) n).toAddMonoidHom

theorem transition_surjective (n r : ℕ)
    (h : Function.Surjective (reductionH j (ℓ ^ r) ℓ n)) :
    Function.Surjective (transition j ℓ n r) :=
  h.comp (orderCongr j (pow_succ ℓ r) n).surjective

/-- The subgroup of compatible finite-level cohomology classes. -/
def compatibleClasses (n : ℕ) := CyclicPowerInverseLimit.compatibleTuples
  (fun r ↦ cohomology j (ℓ ^ r) n) (transition j ℓ n)

/-- The ordinary additive inverse limit is ℤℓ when each level is cyclic and each reduction is onto. -/
def padicEquiv (n : ℕ)
    (onto : ∀ r, Function.Surjective (reductionH j (ℓ ^ r) ℓ n))
    (level : ∀ r, cohomology j (ℓ ^ r) n ≃+ ZMod (ℓ ^ r)) :
    compatibleClasses j ℓ n ≃+ ℤ_[ℓ] :=
  CyclicPowerInverseLimit.padicEquiv ℓ (fun r ↦ cohomology j (ℓ ^ r) n) (transition j ℓ n)
    (fun r ↦ transition_surjective j ℓ n r (onto r)) level

end
end ManuscriptAudit.OpenEtaleCyclicInverseLimit

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.OpenEtaleCyclicInverseLimit.transition_surjective,
      ``ManuscriptAudit.OpenEtaleCyclicInverseLimit.padicEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
