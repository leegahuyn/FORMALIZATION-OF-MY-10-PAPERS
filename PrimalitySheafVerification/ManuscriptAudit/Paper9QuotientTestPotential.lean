import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper9CuspNormOnQuotient
import PrimalitySheafVerification.ManuscriptAudit.Paper9CuspPotentialGlobal

/-! The actual global potential integral localizes to the high-cusp coordinate strip. -/

namespace ManuscriptAudit.Paper9QuotientTestPotential

open MeasureTheory Set Paper9CuspNormOnQuotient Paper9CuspPotentialGlobal
open Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry
open scoped UpperHalfPlane

noncomputable section

def contribution (D : GammaTwoFundamentalDomain) (Y : ℝ) : ℝ :=
  ∫ q, quotientPotential q * normSq Y q ∂D.quotientMeasure

theorem contribution_eq_high_strip (D : GammaTwoFundamentalDomain) (Y : ℝ) (hY : 1 ≤ Y) :
    contribution D Y = ∫ z in GammaTwoHighStripMeasure.strip,
      z.im ^ 6 * Paper9CuspPotentialForm.heightTest Y z.im ^ 2 ∂hyperbolicMeasure := by
  let B := gammaTwoQuotientMk '' GammaTwoHighStripMeasure.strip
  let f : GammaTwoQuotient → ℝ := fun q => quotientPotential q * normSq Y q
  have hB : MeasurableSet B :=
    GammaTwoFundamentalDomain.quotientImage_measurable GammaTwoHighStripMeasure.strip_measurable
  have hF : Measurable f := quotientPotential_measurable.mul (normSq_measurable Y hY)
  have hs : (∫ q, f q ∂D.quotientMeasure) = ∫ q in B, f q ∂D.quotientMeasure := by
    rw [← integral_indicator hB]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro q
    by_cases hq : q ∈ B
    · rw [indicator_of_mem hq]
    · have hz := normSq_zero_outside_highStrip Y hY hq
      rw [indicator_of_notMem hq]
      change quotientPotential q * normSq Y q = 0
      rw [hz, mul_zero]
  unfold contribution
  change (∫ q, f q ∂D.quotientMeasure) = _
  rw [hs]
  change (∫ q, f q ∂D.quotientMeasure.restrict B) = _
  rw [← GammaTwoHighStripMeasure.quotient_strip_measure D]
  have hmk : Measurable gammaTwoQuotientMk := measurable_quotient_mk''
  rw [integral_map hmk.aemeasurable hF.aestronglyMeasurable]
  apply setIntegral_congr_fun GammaTwoHighStripMeasure.strip_measurable
  intro z hz
  have hh : 1 < z.im := hz.1
  change quotientPotential (gammaTwoQuotientMk z) * normSq Y (gammaTwoQuotientMk z) = _
  rw [quotientPotential_at_inf z hh.le, normSq_high Y z hh]

end
end ManuscriptAudit.Paper9QuotientTestPotential

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper9QuotientTestPotential.contribution_eq_high_strip
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
