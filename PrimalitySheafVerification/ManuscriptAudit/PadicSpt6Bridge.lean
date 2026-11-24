import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.PadicBinomialLimit
import PrimalitySheafVerification.Spt6

/-! The exact addition law for the logarithm series defined in Spt6. -/

namespace ManuscriptAudit.PadicSpt6Bridge

/-- The analytic additivity hypothesis in Spt6 follows from the actual
normalized-binomial limit on the open unit ball. -/
theorem spt6_padic_log_additive (p : ℕ) [Fact p.Prime] :
    Spt6.PadicLogFormal.PadicLogAdditive p := by
  intro u v hu hv
  exact PadicBinomialLimit.padicLogSeries_additive p hu hv

/-- The same Spt6 series satisfies the logarithm power law without an
external analytic transfer hypothesis. -/
theorem spt6_principal_unit_log_power (p : ℕ) [Fact p.Prime] {u : ℚ_[p]}
    (hu : ‖u‖ < 1) (n : ℕ) :
    Spt6.PadicLog.logOnePlus ((1 + u) ^ n - 1) = n • Spt6.PadicLog.logOnePlus u :=
  Spt6.PadicLogFormal.logOnePlus_pow_of_additive (spt6_padic_log_additive p) hu n

end ManuscriptAudit.PadicSpt6Bridge

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.PadicSpt6Bridge.spt6_padic_log_additive,
      ``ManuscriptAudit.PadicSpt6Bridge.spt6_principal_unit_log_power] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
