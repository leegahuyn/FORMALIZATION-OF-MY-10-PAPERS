import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspCompactSupportHZero
import PrimalitySheafVerification.ManuscriptAudit.CuspCompactSupportAbsoluteHOne
import PrimalitySheafVerification.ManuscriptAudit.CuspCompactSupportAbsoluteHTwo
import PrimalitySheafVerification.ManuscriptAudit.RatFuncEtaleUnitsHTwo

/-! Actual compactly supported degree-two groups of the cusp and its puncture. -/

namespace ManuscriptAudit.CuspCompactSupportDegreeTwo

open CategoryTheory CuspCompactSupportSequence

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt
  KummerCohomologySequence.affineSiteHasExt

variable (K : Type) [Field K] [IsAlgClosed K] (p : ℕ) [pPrime : Fact p.Prime] [pChar : CharP K p]
  (ℓ : ℕ) [NeZero (ℓ : K)]

include p pPrime pChar

theorem nonempty_cuspHcTwoEquiv (hℓ : 2 ≤ ℓ) :
    Nonempty (cuspHc K (AddCommGrpCat.of (ZMod ℓ)) 2 ≃+ ZMod ℓ) :=
  nonempty_cuspHcTwoEquiv_of_field K p ℓ hℓ
    (RatFuncTsen.rationalFunction_etale_units_HTwo_subsingleton K)

theorem nonempty_punctureHcTwoEquiv (hℓ : 2 ≤ ℓ) :
    Nonempty (punctureHc K (AddCommGrpCat.of (ZMod ℓ)) 2 ≃+ ZMod ℓ) :=
  nonempty_punctureHcTwoEquiv_of_field K p ℓ hℓ
    (RatFuncTsen.rationalFunction_etale_units_HTwo_subsingleton K)

theorem compactSupport_low_degree_cards (hℓ : 2 ≤ ℓ) :
    (Nat.card (cuspHc K (AddCommGrpCat.of (ZMod ℓ)) 0),
      Nat.card (cuspHc K (AddCommGrpCat.of (ZMod ℓ)) 1),
      Nat.card (cuspHc K (AddCommGrpCat.of (ZMod ℓ)) 2)) = (1, 1, ℓ) ∧
    (Nat.card (punctureHc K (AddCommGrpCat.of (ZMod ℓ)) 0),
      Nat.card (punctureHc K (AddCommGrpCat.of (ZMod ℓ)) 1),
      Nat.card (punctureHc K (AddCommGrpCat.of (ZMod ℓ)) 2)) = (1, ℓ, ℓ) := by
  obtain ⟨hP₀, hC₀⟩ := CuspCompactSupportSequence.compactSupportHZero_subsingleton K
    (AddCommGrpCat.of (ZMod ℓ))
  have hP₁ := CuspCompactSupportAbsoluteHOne.punctureHcOneEquiv K p ℓ
  have hC₁ := CuspCompactSupportAbsoluteHOne.cuspHcOne_subsingleton K p ℓ
  obtain ⟨hP₂⟩ := nonempty_punctureHcTwoEquiv K p ℓ hℓ
  obtain ⟨hC₂⟩ := nonempty_cuspHcTwoEquiv K p ℓ hℓ
  rw [Nat.card_eq_one_iff_unique.mpr ⟨hC₀, ⟨0⟩⟩,
    Nat.card_eq_one_iff_unique.mpr ⟨hC₁, ⟨0⟩⟩,
    Nat.card_eq_one_iff_unique.mpr ⟨hP₀, ⟨0⟩⟩,
    Nat.card_congr hC₂.toEquiv, Nat.card_congr hP₁.toEquiv,
    Nat.card_congr hP₂.toEquiv, Nat.card_zmod]
  exact ⟨rfl, rfl⟩

end ManuscriptAudit.CuspCompactSupportDegreeTwo

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CuspCompactSupportDegreeTwo.nonempty_cuspHcTwoEquiv,
      ``ManuscriptAudit.CuspCompactSupportDegreeTwo.nonempty_punctureHcTwoEquiv,
      ``ManuscriptAudit.CuspCompactSupportDegreeTwo.compactSupport_low_degree_cards] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
