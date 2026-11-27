import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CoulombNegativeQuotientForm
import PrimalitySheafVerification.ManuscriptAudit.GammaTwoProfileIntegrability

/-! Every bounded real multiplication potential leaves the literal negative form unbounded below. -/

namespace ManuscriptAudit.CoulombBoundedQuotientPotential

open MeasureTheory CoulombScaledCuspForms CoulombNegativeQuotientForm
open GammaTwoProfileIntegrability
open Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry

noncomputable section

theorem integrable_pointMass (D : GammaTwoFundamentalDomain) (r : ℝ) (hr : 1 ≤ r) :
    Integrable (pointMass r) D.quotientMeasure := by
  have hC : Continuous (massDensity r) := (amplitude_smooth r).continuous.pow 2
  have hz (y : ℝ) (hy : y ≤ 2 ∨ 5 ≤ y) : massDensity r y = 0 := by
    rw [massDensity, amplitude_zero r y hr hy]
    norm_num
  exact integrable_quotient_profile D _ hC (fun y hy => hz y (Or.inl (by linarith)))
    (b := 5) (fun y hy => hz y (Or.inr hy.le))

def potentialIntegral (D : GammaTwoFundamentalDomain) (V : GammaTwoQuotient → ℝ) (r : ℝ) : ℝ :=
  ∫ q, V q * pointMass r q ∂D.quotientMeasure

theorem potentialIntegral_le_mass (D : GammaTwoFundamentalDomain)
    (V : GammaTwoQuotient → ℝ) (hV : Measurable V) {B : ℝ} (hB : ∀ q, ‖V q‖ ≤ B)
    (r : ℝ) (hr : 1 ≤ r) :
    potentialIntegral D V r ≤ B * massOnQuotient D r := by
  have hM := integrable_pointMass D r hr
  have hVI : Integrable (fun q => V q * pointMass r q) D.quotientMeasure :=
    hM.bdd_mul hV.aestronglyMeasurable (Filter.Eventually.of_forall hB)
  have hp (q : GammaTwoQuotient) : V q * pointMass r q ≤ B * pointMass r q := by
    apply mul_le_mul_of_nonneg_right
    · exact (le_abs_self (V q)).trans (by simpa only [Real.norm_eq_abs] using hB q)
    · unfold pointMass massDensity
      positivity
  unfold potentialIntegral massOnQuotient
  rw [← integral_const_mul]
  exact integral_mono hVI (hM.const_mul B) hp

theorem bounded_potential_form_no_mass_lower_bound (D : GammaTwoFundamentalDomain)
    (V : GammaTwoQuotient → ℝ) (hV : Measurable V) {B : ℝ} (hB : ∀ q, ‖V q‖ ≤ B)
    (b : ℝ) :
    ∃ r : ℝ, 1 ≤ r ∧ 0 < massOnQuotient D r ∧
      -energyOnQuotient D r + potentialIntegral D V r < b * massOnQuotient D r := by
  obtain ⟨r, hr, hM, hE⟩ := negative_quotient_form_no_mass_lower_bound D (b - B)
  refine ⟨r, hr, hM, ?_⟩
  have hP := potentialIntegral_le_mass D V hV hB r hr
  calc
    _ < (b - B) * massOnQuotient D r + potentialIntegral D V r := add_lt_add_right hE _
    _ ≤ (b - B) * massOnQuotient D r + B * massOnQuotient D r := by
      linarith only [hP]
    _ = b * massOnQuotient D r := by ring

end
end ManuscriptAudit.CoulombBoundedQuotientPotential

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CoulombBoundedQuotientPotential.integrable_pointMass,
      ``ManuscriptAudit.CoulombBoundedQuotientPotential.potentialIntegral_le_mass,
      ``ManuscriptAudit.CoulombBoundedQuotientPotential.bounded_potential_form_no_mass_lower_bound] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"

