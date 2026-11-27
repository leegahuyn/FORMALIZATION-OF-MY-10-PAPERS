import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ExactFiniteAddGroups
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleCoefficientReduction

/-! A cyclic compact-cohomology degree propagates surjectivity of coefficient reduction to the previous degree. -/

namespace ManuscriptAudit.OpenEtaleCoefficientReduction

open AlgebraicGeometry CategoryTheory
open OpenComplementRationalPointCohomology (extensionH)

noncomputable section

set_option backward.isDefEq.respectTransparency false
attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]
variable (a b : ℕ) [NeZero a] [NeZero b]

/-- If the three higher compact groups are cyclic of their coefficient orders,
surjectivity of the higher reduction implies surjectivity of the previous one. -/
theorem reductionH_surjective_of_next_cyclic (n : ℕ)
    (e₁ : extensionH j (AddCommGrpCat.of (ZMod b)) (n + 1) ≃+ ZMod b)
    (e₂ : extensionH j (AddCommGrpCat.of (ZMod (a * b))) (n + 1) ≃+ ZMod (a * b))
    (e₃ : extensionH j (AddCommGrpCat.of (ZMod a)) (n + 1) ≃+ ZMod a)
    (hg : Function.Surjective (reductionH j a b (n + 1))) :
    Function.Surjective (reductionH j a b n) := by
  letI : NeZero (a * b) := ⟨Nat.mul_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
  letI : Finite (extensionH j (AddCommGrpCat.of (ZMod b)) (n + 1)) := Finite.of_injective e₁ e₁.injective
  letI : Finite (extensionH j (AddCommGrpCat.of (ZMod (a * b))) (n + 1)) := Finite.of_injective e₂ e₂.injective
  letI : Finite (extensionH j (AddCommGrpCat.of (ZMod a)) (n + 1)) := Finite.of_injective e₃ e₃.injective
  have hCard : Nat.card (extensionH j (AddCommGrpCat.of (ZMod (a * b))) (n + 1)) =
      Nat.card (extensionH j (AddCommGrpCat.of (ZMod a)) (n + 1)) *
      Nat.card (extensionH j (AddCommGrpCat.of (ZMod b)) (n + 1)) := by
    simp only [Nat.card_congr e₁.toEquiv, Nat.card_congr e₂.toEquiv, Nat.card_congr e₃.toEquiv, Nat.card_zmod]
  have hInj : Function.Injective (inclusionH j a b (n + 1)) :=
    ExactFiniteAddGroups.first_injective _ _ (inclusion_reduction_exact j a b (n + 1)) hg hCard
  exact reductionH_surjective_of_next_injective j a b n hInj

end
end ManuscriptAudit.OpenEtaleCoefficientReduction

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.OpenEtaleCoefficientReduction.reductionH_surjective_of_next_cyclic
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
