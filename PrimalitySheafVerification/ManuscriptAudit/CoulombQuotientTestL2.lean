import Lean.Util.CollectAxioms
import Mathlib.MeasureTheory.Function.L2Space
import PrimalitySheafVerification.ManuscriptAudit.CoulombBoundedQuotientPotential

/-! The horizontal co-closed tests are actual quotient (L^2) vectors.
The coefficient in the orthonormal horizontal frame is (y a_r(y)). -/

namespace ManuscriptAudit.CoulombQuotientTestL2

open MeasureTheory CoulombScaledCuspForms CoulombNegativeQuotientForm
open CoulombBoundedQuotientPotential GammaTwoQuotientHeightIntegral
open Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry

noncomputable section

abbrev quotientL2 (D : GammaTwoFundamentalDomain) := Lp ℝ 2 D.quotientMeasure

def horizontalCoefficient (r : ℝ) (q : GammaTwoQuotient) : ℝ :=
  quotientHeight q * amplitude r (quotientHeight q)

theorem horizontalCoefficient_measurable (r : ℝ) : Measurable (horizontalCoefficient r) :=
  quotientHeight_measurable.mul ((amplitude_smooth r).continuous.measurable.comp
    quotientHeight_measurable)

theorem horizontalCoefficient_sq (r : ℝ) (q : GammaTwoQuotient) :
    horizontalCoefficient r q ^ 2 = pointMass r q := by
  unfold horizontalCoefficient pointMass massDensity
  ring

theorem horizontalCoefficient_memLp (D : GammaTwoFundamentalDomain) (r : ℝ) (hr : 1 ≤ r) :
    MemLp (horizontalCoefficient r) 2 D.quotientMeasure := by
  apply (memLp_two_iff_integrable_sq (horizontalCoefficient_measurable r).aestronglyMeasurable).mpr
  convert integrable_pointMass D r hr using 1
  funext q
  exact horizontalCoefficient_sq r q

/-- The genuine quotient (L^2) class given by the horizontal test. -/
def testVector (D : GammaTwoFundamentalDomain) (r : ℝ) (hr : 1 ≤ r) : quotientL2 D :=
  (horizontalCoefficient_memLp D r hr).toLp (horizontalCoefficient r)

theorem testVector_norm_sq (D : GammaTwoFundamentalDomain) (r : ℝ) (hr : 1 ≤ r) :
    ‖testVector D r hr‖ ^ 2 = massOnQuotient D r := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def, massOnQuotient]
  have h : (testVector D r hr : GammaTwoQuotient → ℝ) =ᵐ[D.quotientMeasure]
      horizontalCoefficient r := (horizontalCoefficient_memLp D r hr).coeFn_toLp
  apply integral_congr_ae
  filter_upwards [h] with q hq
  rw [hq, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  exact horizontalCoefficient_sq r q

end
end ManuscriptAudit.CoulombQuotientTestL2

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CoulombQuotientTestL2.horizontalCoefficient_sq,
      ``ManuscriptAudit.CoulombQuotientTestL2.horizontalCoefficient_memLp,
      ``ManuscriptAudit.CoulombQuotientTestL2.testVector_norm_sq] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
