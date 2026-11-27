import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspCompactSupportAbsoluteHTwo
import PrimalitySheafVerification.ManuscriptAudit.RatFuncEtaleUnitsHTwo

/-! Actual compactly supported degree-two groups of the cusp and its puncture. -/

namespace ManuscriptAudit.CuspCompactSupportDegreeTwo

open CategoryTheory CuspCompactSupportSequence

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt
  KummerCohomologySequence.affineSiteHasExt

variable (K : Type) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
  (ℓ : ℕ) [NeZero (ℓ : K)]

theorem nonempty_cuspHcTwoEquiv (hℓ : 2 ≤ ℓ) :
    Nonempty (cuspHc K (AddCommGrpCat.of (ZMod ℓ)) 2 ≃+ ZMod ℓ) :=
  nonempty_cuspHcTwoEquiv_of_field K p ℓ hℓ
    (RatFuncTsen.rationalFunction_etale_units_HTwo_subsingleton K)

theorem nonempty_punctureHcTwoEquiv (hℓ : 2 ≤ ℓ) :
    Nonempty (punctureHc K (AddCommGrpCat.of (ZMod ℓ)) 2 ≃+ ZMod ℓ) :=
  nonempty_punctureHcTwoEquiv_of_field K p ℓ hℓ
    (RatFuncTsen.rationalFunction_etale_units_HTwo_subsingleton K)

end ManuscriptAudit.CuspCompactSupportDegreeTwo

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CuspCompactSupportDegreeTwo.nonempty_cuspHcTwoEquiv,
      ``ManuscriptAudit.CuspCompactSupportDegreeTwo.nonempty_punctureHcTwoEquiv] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
