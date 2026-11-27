import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CoulombCompactTruncationForm

/-! Paper 10, physical p. 495, §4.7.6. On the same native compact-cut
tests, the displayed positive Rayleigh form has a mass lower bound,
while the negative expectation from equation (4.43) has none. -/

namespace ManuscriptAudit.CoulombCompactOppositeForms

open MeasureTheory CoulombNegativeQuotientForm CoulombBoundedQuotientPotential
open CoulombCompactTruncationForm
open Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry

noncomputable section

private theorem potentialIntegral_neg (D : GammaTwoFundamentalDomain)
    (V : GammaTwoQuotient → ℝ) (r : ℝ) :
    potentialIntegral D (fun q => -V q) r = -potentialIntegral D V r := by
  unfold potentialIntegral
  simp_rw [neg_mul]
  exact integral_neg _

private theorem potentialIntegral_lower (D : GammaTwoFundamentalDomain)
    (V : GammaTwoQuotient → ℝ) (hV : Measurable V) {B : ℝ} (hB : ∀ q, ‖V q‖ ≤ B)
    (r : ℝ) (hr : 1 ≤ r) :
    (-B) * massOnQuotient D r ≤ potentialIntegral D V r := by
  have hN : ∀ q, ‖-V q‖ ≤ B := fun q => by simpa only [norm_neg] using hB q
  have h := potentialIntegral_le_mass D (fun q => -V q) hV.neg hN r hr
  rw [potentialIntegral_neg] at h
  calc
    _ = -(B * massOnQuotient D r) := by ring
    _ ≤ -(-potentialIntegral D V r) := neg_le_neg h
    _ = _ := neg_neg _

private theorem truncated_energy_nonneg (D : GammaTwoFundamentalDomain) (Y r : ℝ) :
    0 ≤ energyOnTruncation D Y r := by
  unfold energyOnTruncation
  apply integral_nonneg
  intro q
  unfold pointEnergy energyDensity
  positivity

/-- The displayed positive form in §4.7.6 has the proposed lower
bound on these actual compactly truncated tests. -/
theorem positive_form_mass_lower_bound (D : GammaTwoFundamentalDomain)
    (Y : ℝ) (hY : 5 ≤ Y) (V : GammaTwoQuotient → ℝ) (hV : Measurable V)
    {B : ℝ} (hB : ∀ q, ‖V q‖ ≤ B) (r : ℝ) (hr : 1 ≤ r) :
    (-B) * massOnTruncation D Y r ≤ energyOnTruncation D Y r + potentialOnTruncation D Y V r := by
  obtain ⟨hMass, _, hPot⟩ := truncation_integrals_eq D Y hY V r hr
  have hl : (-B) * massOnTruncation D Y r ≤ potentialOnTruncation D Y V r := by
    rw [hMass, hPot]
    exact potentialIntegral_lower D V hV hB r hr
  linarith only [hl, truncated_energy_nonneg D Y r]

/-- On one and the same nonzero test the negative and positive
Rayleigh quotients lie on opposite sides of the advertised lower bound. -/
theorem opposite_rayleigh_forms_disagree (D : GammaTwoFundamentalDomain)
    (Y : ℝ) (hY : 5 ≤ Y) (V : GammaTwoQuotient → ℝ) (hV : Measurable V)
    {B : ℝ} (hB : ∀ q, ‖V q‖ ≤ B) :
    ∃ r : ℝ, 1 ≤ r ∧ 0 < massOnTruncation D Y r ∧
      (-energyOnTruncation D Y r + potentialOnTruncation D Y V r) /
        massOnTruncation D Y r < -B ∧
      -B ≤ (energyOnTruncation D Y r + potentialOnTruncation D Y V r) /
        massOnTruncation D Y r := by
  obtain ⟨r, hr, hm, hNeg⟩ := truncated_form_no_mass_lower_bound D Y hY V hV hB (-B)
  exact ⟨r, hr, hm, (div_lt_iff₀ hm).mpr hNeg,
    (le_div_iff₀ hm).mpr (positive_form_mass_lower_bound D Y hY V hV hB r hr)⟩

end
end ManuscriptAudit.CoulombCompactOppositeForms

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CoulombCompactOppositeForms.positive_form_mass_lower_bound,
      ``ManuscriptAudit.CoulombCompactOppositeForms.opposite_rayleigh_forms_disagree] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
