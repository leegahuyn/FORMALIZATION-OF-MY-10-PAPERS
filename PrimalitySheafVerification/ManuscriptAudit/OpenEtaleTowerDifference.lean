import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.SequentialInverseLimitDifference
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleCyclicInverseLimit

/-! The countable product difference for the actual prime-power compact cohomology reductions. -/

namespace ManuscriptAudit.OpenEtaleTowerDifference

open AlgebraicGeometry CategoryTheory
open OpenComplementRationalPointCohomology (extensionH)
open OpenEtaleCyclicInverseLimit (compatibleClasses transition transition_surjective)
open OpenEtaleCoefficientReduction (reductionH)

noncomputable section

set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]
variable (ℓ : ℕ) [Fact ℓ.Prime]

local instance prime_neZero : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
local instance power_neZero (r : ℕ) : NeZero (ℓ ^ r) :=
  ⟨pow_ne_zero r (Fact.out : ℓ.Prime).ne_zero⟩

abbrev level (n r : ℕ) := extensionH j (AddCommGrpCat.of (ZMod (ℓ ^ r))) n

/-- The product difference using the native cohomology reductions. -/
def difference (n : ℕ) : (∀ r, level j ℓ n r) →+ (∀ r, level j ℓ n r) :=
  SequentialInverseLimitDifference.productDifference (level j ℓ n) (transition j ℓ n)

/-- The product difference has the actual compatible-class group as kernel. -/
theorem ker_difference (n : ℕ) :
    (difference j ℓ n).ker = compatibleClasses j ℓ n := by
    ext x
    change SequentialInverseLimitDifference.productDifference (level j ℓ n) (transition j ℓ n) x = 0 ↔
      ∀ r, transition j ℓ n r (x (r + 1)) = x r
    exact SequentialInverseLimitDifference.productDifference_eq_zero_iff
      (level j ℓ n) (transition j ℓ n) x

/-- Surjectivity of the actual coefficient reductions implies surjectivity of the product difference. -/
theorem difference_surjective (n : ℕ)
    (onto : ∀ r, Function.Surjective (reductionH j (ℓ ^ r) ℓ n)) :
    Function.Surjective (difference j ℓ n) :=
  SequentialInverseLimitDifference.productDifference_surjective (level j ℓ n) (transition j ℓ n)
    (fun r ↦ transition_surjective j ℓ n r (onto r))

/-- Compatible classes vanish when the actual groups at all finite levels vanish. -/
theorem compatibleClasses_subsingleton (n : ℕ)
    (h : ∀ r, Subsingleton (level j ℓ n r)) : Subsingleton (compatibleClasses j ℓ n) :=
  ⟨fun x y ↦ Subtype.ext (funext fun r ↦ (h r).elim _ _)⟩

end
end ManuscriptAudit.OpenEtaleTowerDifference

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.OpenEtaleTowerDifference.ker_difference,
      ``ManuscriptAudit.OpenEtaleTowerDifference.difference_surjective,
      ``ManuscriptAudit.OpenEtaleTowerDifference.compatibleClasses_subsingleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
