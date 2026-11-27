import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CoulombBoundedQuotientPotential

/-! The literal negative form also has no mass lower bound after
restriction to the measured compact three-cusp truncation. The same
tests have support away from all cusp cuts for (Y > 5). -/

namespace ManuscriptAudit.CoulombCompactTruncationForm

open Set MeasureTheory CoulombScaledCuspForms CoulombNegativeQuotientForm
open CoulombBoundedQuotientPotential GammaTwoQuotientHeightIntegral
open Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry
open scoped MatrixGroups UpperHalfPlane Topology

noncomputable section

def truncation (Y : ℝ) : Set GammaTwoQuotient :=
  gammaTwoQuotientMk '' gammaTwoThreeCuspTruncation Y

theorem truncation_isCompact (Y : ℝ) : IsCompact (truncation Y) :=
  (gammaTwoThreeCuspTruncation_isCompact Y).image gammaTwoQuotientMk_isOpenQuotientMap.continuous

private theorem im_smul_eq_of_bottom_left_zero (g : SL(2, ℤ)) (z : ℍ) (hc : g 1 0 = 0) :
    (g • z).im = z.im := by
  have hdet : g 0 0 * g 1 1 = 1 := by
    simpa only [Matrix.det_fin_two, hc, mul_zero, sub_zero] using g.det_coe
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hdet with ⟨_, hd⟩ | ⟨_, hd⟩ <;>
    rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply] <;>
    norm_num [hc, hd, Complex.normSq_apply]

private theorem upper_height_bound (Y : ℝ) (hY : 1 ≤ Y) (z : ℍ)
    (hLow : 1 < z.im) (hHigh : z.im ≤ Y) (g : SL(2, ℤ)) : (g • z).im ≤ Y := by
  by_cases hg : g 1 0 = 0
  · rwa [im_smul_eq_of_bottom_left_zero g z hg]
  · exact (HighInfinityCusp.height_lt_one_of_bottom_left_ne_zero g z hLow hg).le.trans hY

/-- Every quotient point in the support heights has a representative
in the actual closed six-tile three-cusp truncation. -/
theorem mem_truncation_of_height (Y : ℝ) (hY : 1 ≤ Y) (q : GammaTwoQuotient)
    (hLow : 1 < quotientHeight q) (hHigh : quotientHeight q ≤ Y) :
    q ∈ truncation Y := by
  obtain ⟨z, hz, heq⟩ := mem_strip_image_of_height hLow
  have hzLow : 1 < z.im := hz.1
  have hzHigh : z.im ≤ Y := by
    rw [← quotientHeight_high z hzLow.le, heq]
    exact hHigh
  obtain ⟨a, ha⟩ := gammaTwoClosedTileCarrier_orbit_covers z
  obtain ⟨γ, hγ⟩ := effective_exists_gamma a
  refine ⟨a • z, ⟨ha, ?_⟩, (gammaTwoQuotientMk_smul a z).trans heq⟩
  intro κ t _ht
  change ((gammaTwoCosetRep t)⁻¹ • (a • z)).im ≤ gammaTwoCuspLevel Y
  rw [hγ z]
  change ((gammaTwoCosetRep t)⁻¹ • ((γ : SL(2, ℤ)) • z)).im ≤ gammaTwoCuspLevel Y
  rw [← mul_smul]
  exact (upper_height_bound Y hY z hzLow hzHigh _).trans (le_max_right _ _)

private theorem outside_height (Y : ℝ) (hY : 5 ≤ Y) (q : GammaTwoQuotient)
    (hq : q ∉ truncation Y) : quotientHeight q < 2 ∨ 5 < quotientHeight q := by
  by_cases hLow : 1 < quotientHeight q
  · right
    have hHigh : Y < quotientHeight q := lt_of_not_ge
      (fun h => hq (mem_truncation_of_height Y (by linarith) q hLow h))
    exact hY.trans_lt hHigh
  · left
    exact (le_of_not_gt hLow).trans_lt (by norm_num)

private theorem mass_zero_outside (Y : ℝ) (hY : 5 ≤ Y) (r : ℝ) (hr : 1 ≤ r)
    (q : GammaTwoQuotient) (hq : q ∉ truncation Y) : pointMass r q = 0 := by
  have h := outside_height Y hY q hq
  rw [pointMass, massDensity, amplitude_zero r _ hr (h.imp le_of_lt le_of_lt)]
  ring

private theorem deriv_zero (r y : ℝ) (hr : 1 ≤ r) (h : y < 2 ∨ 5 < y) :
    deriv (amplitude r) y = 0 := by
  have hz : amplitude r =ᶠ[𝓝 y] (fun _ : ℝ => (0 : ℝ)) := by
    rcases h with h | h
    · filter_upwards [Iio_mem_nhds h] with t ht
      exact amplitude_zero r t hr (Or.inl (le_of_lt ht))
    · filter_upwards [Ioi_mem_nhds h] with t ht
      exact amplitude_zero r t hr (Or.inr (le_of_lt ht))
  simpa only [deriv_const] using hz.deriv_eq

private theorem energy_zero_outside (Y : ℝ) (hY : 5 ≤ Y) (r : ℝ) (hr : 1 ≤ r)
    (q : GammaTwoQuotient) (hq : q ∉ truncation Y) : pointEnergy r q = 0 := by
  have h := outside_height Y hY q hq
  rw [pointEnergy, energyDensity, amplitude_zero r _ hr (h.imp le_of_lt le_of_lt),
    deriv_zero r _ hr h]
  ring

private theorem integral_eq_of_zero_outside (D : GammaTwoFundamentalDomain) (Y : ℝ)
    (f : GammaTwoQuotient → ℝ) (hz : ∀ q ∉ truncation Y, f q = 0) :
    (∫ q in truncation Y, f q ∂D.quotientMeasure) = ∫ q, f q ∂D.quotientMeasure := by
  rw [← integral_indicator (truncation_isCompact Y).isClosed.measurableSet]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro q
  by_cases hq : q ∈ truncation Y
  · rw [indicator_of_mem hq]
  · rw [indicator_of_notMem hq, hz q hq]

def massOnTruncation (D : GammaTwoFundamentalDomain) (Y r : ℝ) : ℝ :=
  ∫ q in truncation Y, pointMass r q ∂D.quotientMeasure

def energyOnTruncation (D : GammaTwoFundamentalDomain) (Y r : ℝ) : ℝ :=
  ∫ q in truncation Y, pointEnergy r q ∂D.quotientMeasure

def potentialOnTruncation (D : GammaTwoFundamentalDomain) (Y : ℝ)
    (V : GammaTwoQuotient → ℝ) (r : ℝ) : ℝ :=
  ∫ q in truncation Y, V q * pointMass r q ∂D.quotientMeasure

/-- All three integrals agree with their full-quotient values for these tests. -/
theorem truncation_integrals_eq (D : GammaTwoFundamentalDomain) (Y : ℝ) (hY : 5 ≤ Y)
    (V : GammaTwoQuotient → ℝ) (r : ℝ) (hr : 1 ≤ r) :
    massOnTruncation D Y r = massOnQuotient D r ∧
      energyOnTruncation D Y r = energyOnQuotient D r ∧
      potentialOnTruncation D Y V r = potentialIntegral D V r := by
  refine ⟨integral_eq_of_zero_outside D Y _ (mass_zero_outside Y hY r hr),
    integral_eq_of_zero_outside D Y _ (energy_zero_outside Y hY r hr), ?_⟩
  apply integral_eq_of_zero_outside
  intro q hq
  rw [mass_zero_outside Y hY r hr q hq, mul_zero]

/-- Every bounded measurable real potential leaves the compactly
truncated negative differential form unbounded relative to mass. -/
theorem truncated_form_no_mass_lower_bound (D : GammaTwoFundamentalDomain)
    (Y : ℝ) (hY : 5 ≤ Y) (V : GammaTwoQuotient → ℝ) (hV : Measurable V)
    {B : ℝ} (hB : ∀ q, ‖V q‖ ≤ B) (b : ℝ) :
    ∃ r : ℝ, 1 ≤ r ∧ 0 < massOnTruncation D Y r ∧
      -energyOnTruncation D Y r + potentialOnTruncation D Y V r <
        b * massOnTruncation D Y r := by
  obtain ⟨r, hr, hm, hf⟩ := bounded_potential_form_no_mass_lower_bound D V hV hB b
  obtain ⟨hM, hE, hP⟩ := truncation_integrals_eq D Y hY V r hr
  exact ⟨r, hr, hM.symm ▸ hm, by rwa [hM, hE, hP]⟩

end
end ManuscriptAudit.CoulombCompactTruncationForm

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CoulombCompactTruncationForm.truncation_isCompact,
      ``ManuscriptAudit.CoulombCompactTruncationForm.mem_truncation_of_height,
      ``ManuscriptAudit.CoulombCompactTruncationForm.truncation_integrals_eq,
      ``ManuscriptAudit.CoulombCompactTruncationForm.truncated_form_no_mass_lower_bound] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
