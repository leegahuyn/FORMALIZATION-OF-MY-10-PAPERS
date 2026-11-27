import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CoulombCuspEnergyIdentity
import PrimalitySheafVerification.ManuscriptAudit.CoulombQuotientTestL2
import PrimalitySheafVerification.ManuscriptAudit.Paper10RemainderCoercivity

/-!
# The repaired coercive bound on the actual compact co-closed cusp tests

The sum of mass and covariant energies is the native first Sobolev
energy of these horizontal tests. A global remainder absorption
estimate gives a quantitative lower bound for this energy.
-/

namespace ManuscriptAudit.Paper10CuspCoerciveBound

open MeasureTheory CoulombQuotientTestL2 CoulombNegativeQuotientForm
open CoulombCuspEnergyIdentity Paper10RemainderCoercivity
open Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry

noncomputable section

def sobolevEnergy (D : GammaTwoFundamentalDomain) (r : ℝ) : ℝ :=
  massOnQuotient D r + energyOnQuotient D r

theorem exterior_energy_nonnegative (D : GammaTwoFundamentalDomain) (r : ℝ)
    (hr : 1 ≤ r) : 0 ≤ exteriorEnergyOnQuotient D r := by
  rw [exterior_energy_on_quotient_eq D r hr, exteriorEnergy]
  apply mul_nonneg (by norm_num)
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro y _
  exact sq_nonneg _

theorem measured_mass_nonnegative (D : GammaTwoFundamentalDomain) (r : ℝ)
    (hr : 1 ≤ r) : 0 ≤ massOnQuotient D r := by
  rw [← testVector_norm_sq D r hr]
  exact sq_nonneg _

theorem cusp_HOne_coercive_lower_bound (D : GammaTwoFundamentalDomain) (r : ℝ)
    (hr : 1 ≤ r) (lead m v R cF cM epsV epsR epsM C0 CV CR : ℝ)
    (hLead : cF * exteriorEnergyOnQuotient D r ≤ lead)
    (hMass : cM * massOnQuotient D r - C0 ≤ m)
    (hV : |v| ≤ epsV * exteriorEnergyOnQuotient D r + CV)
    (hR : |R| ≤ epsR * exteriorEnergyOnQuotient D r +
      epsM * massOnQuotient D r + CR) :
    min (cF - epsV - epsR) ((cM - epsM)/2) * sobolevEnergy D r - (C0+CV+CR)
      ≤ lead + m + v + R := by
  let c := min (cF - epsV - epsR) ((cM - epsM)/2)
  let e := exteriorEnergyOnQuotient D r
  let b := massOnQuotient D r
  have hce : c ≤ cF - epsV - epsR := min_le_left _ _
  have hcb : 2*c ≤ cM - epsM := by
    dsimp [c]
    linarith only [min_le_right (cF - epsV - epsR) ((cM - epsM)/2)]
  have hE : 0 ≤ e := exterior_energy_nonnegative D r hr
  have hB : 0 ≤ b := measured_mass_nonnegative D r hr
  have h := global_absorption_lower_bound e b lead m v R cF cM epsV epsR epsM C0 CV CR
    hLead hMass hV hR
  change c * (b + energyOnQuotient D r) - (C0+CV+CR) ≤ lead+m+v+R
  rw [actual_coclosed_cusp_energy_identity D r hr]
  change c * (b + (b + e)) - (C0+CV+CR) ≤ lead+m+v+R
  nlinarith only [h, mul_le_mul_of_nonneg_right hce hE, mul_le_mul_of_nonneg_right hcb hB]

theorem positive_absorption_coefficient {cF cM epsV epsR epsM : ℝ}
    (hF : epsV + epsR < cF) (hM : epsM < cM) :
    0 < min (cF - epsV - epsR) ((cM - epsM)/2) :=
  lt_min (by linarith) (by linarith)

end
end ManuscriptAudit.Paper10CuspCoerciveBound

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper10CuspCoerciveBound.exterior_energy_nonnegative,
      ``ManuscriptAudit.Paper10CuspCoerciveBound.measured_mass_nonnegative,
      ``ManuscriptAudit.Paper10CuspCoerciveBound.cusp_HOne_coercive_lower_bound,
      ``ManuscriptAudit.Paper10CuspCoerciveBound.positive_absorption_coefficient] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
