import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.GammaTwoQuotientHeightIntegral
import PrimalitySheafVerification.ManuscriptAudit.Paper9CuspLogMass

/-! Exact log-height integration on the finite slabs of the genuine quotient cusp. -/

namespace ManuscriptAudit.Paper9QuotientLogProfile

open Filter MeasureTheory Set GammaTwoQuotientHeightIntegral
open Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry

noncomputable section

def clipped (F : ℝ → ℝ) (a b y : ℝ) : ℝ :=
  (Ioc a b).indicator (fun t => F (Real.log t) * t⁻¹) y

def density (F : ℝ → ℝ) (a b : ℝ) (q : GammaTwoQuotient) : ℝ :=
  quotientHeight q ^ 2 * clipped F a b (quotientHeight q)

theorem density_at_height (F : ℝ → ℝ) {a b : ℝ} {q : GammaTwoQuotient}
    (hq : quotientHeight q ∈ Ioc a b) (hPos : 0 < quotientHeight q) :
    density F a b q = quotientHeight q * F (Real.log (quotientHeight q)) := by
  rw [density, clipped, indicator_of_mem hq]
  generalize F (Real.log (quotientHeight q)) = c
  field_simp [hPos.ne'] <;> ring

theorem integral_density (D : GammaTwoFundamentalDomain) (F : ℝ → ℝ) (hF : Continuous F)
    {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (∫ q, density F a b q ∂D.quotientMeasure) = 2 * ∫ t in Real.log a..Real.log b, F t := by
  have hMeas : Measurable (clipped F a b) :=
    ((hF.measurable.comp Real.measurable_log).mul measurable_inv).indicator measurableSet_Ioc
  have hZero (y : ℝ) (hy : y ≤ 1) : clipped F a b y = 0 :=
    indicator_of_notMem (fun h : y ∈ Ioc a b => (not_lt_of_ge (hy.trans ha.le)) h.1) _
  have hInterval :
      (∫ y in Ioi (1 : ℝ), clipped F a b y) =
        ∫ y in a..b, F (Real.log y) * y⁻¹ := by
    rw [intervalIntegral.integral_of_le hab, ← integral_indicator measurableSet_Ioc,
      ← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro y
    by_cases hy : y ∈ Ioi (1 : ℝ)
    · rw [indicator_of_mem hy] <;> rfl
    · rw [indicator_of_notMem hy,
        indicator_of_notMem (fun h : y ∈ Ioc a b => hy (ha.trans h.1))]
  unfold density
  rw [integral_profile D _ hMeas hZero, hInterval,
    Paper9CuspLogMass.log_substitution F hF (zero_lt_one.trans ha) hab]

end
end ManuscriptAudit.Paper9QuotientLogProfile

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper9QuotientLogProfile.density_at_height,
      ``ManuscriptAudit.Paper9QuotientLogProfile.integral_density] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
