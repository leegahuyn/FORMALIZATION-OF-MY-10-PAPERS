import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.GammaTwoHighStripIntegral
import PrimalitySheafVerification.ManuscriptAudit.Paper9QuotientTestPotential

/-! The actual quotient potential violates the stated width-two energy estimate. -/

namespace ManuscriptAudit.Paper9QuotientPotentialHeight

open MeasureTheory Set Paper9QuotientTestPotential Paper9CuspPotentialForm
open HyperbolicCuspGaugeTest
open Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry

noncomputable section

private def heightDensity (Y y : ℝ) : ℝ := y ^ 4 * heightTest Y y ^ 2

private theorem heightDensity_zero (Y y : ℝ) (h : y ≤ Y + 2 ∨ Y + 5 ≤ y) :
    heightDensity Y y = 0 := by rw [heightDensity, heightTest_zero Y y h, zero_pow (by decide), mul_zero]

private theorem height_integral_fixed (Y : ℝ) (hY : 1 ≤ Y) :
    (∫ y in Ioi (1 : ℝ), heightDensity Y y) =
      ∫ t : ℝ in (1 : ℝ)..6, potentialDensity Y t := by
  let f := heightDensity Y
  let A := Ioc (Y + 1) (Y + 6)
  have hA : MeasurableSet A := measurableSet_Ioc
  have hSub : A ⊆ Ioi (1 : ℝ) := by intro y hy; exact lt_of_le_of_lt (by linarith) hy.1
  have hRest : (∫ y in Ioi (1 : ℝ), f y) = ∫ y in A, f y := by
    rw [← integral_indicator measurableSet_Ioi, ← integral_indicator hA]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro y
    by_cases hy : y ∈ A
    · rw [indicator_of_mem hy, indicator_of_mem (hSub hy)]
    · rw [indicator_of_notMem hy]
      by_cases h1 : y ∈ Ioi (1 : ℝ)
      · rw [indicator_of_mem h1]
        have hn : y ≤ Y + 1 ∨ Y + 6 < y := by
          by_cases h' : Y + 1 < y
          · exact Or.inr (lt_of_not_ge fun hh => hy ⟨h', hh⟩)
          · exact Or.inl (le_of_not_gt h')
        exact heightDensity_zero Y y (hn.imp (by intro h; linarith) (by intro h; linarith))
      · rw [indicator_of_notMem h1]
  calc
    _ = ∫ y in A, f y := hRest
    _ = ∫ y : ℝ in (Y + 1)..(Y + 6), f y :=
      (intervalIntegral.integral_of_le (by linarith : Y + 1 ≤ Y + 6)).symm
    _ = ∫ t : ℝ in (1 : ℝ)..6, f (Y + t) :=
      (intervalIntegral.integral_comp_add_left f Y).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro t _
      change (Y + t) ^ 4 * cuspBump (Y + t - Y) ^ 2 = (Y + t) ^ 4 * cuspBump t ^ 2
      rw [show Y + t - Y = t by ring]

theorem contribution_eq_coordinate (D : GammaTwoFundamentalDomain) (Y : ℝ) (hY : 1 ≤ Y) :
    contribution D Y = potentialContribution Y := by
  rw [contribution_eq_high_strip D Y hY]
  have hp (y : ℝ) : y ^ 6 * heightTest Y y ^ 2 = y ^ 2 * heightDensity Y y := by
    unfold heightDensity
    ring
  simp_rw [hp]
  rw [GammaTwoHighStripIntegral.height_integral, height_integral_fixed Y hY] <;> rfl

theorem contribution_no_bound (D : GammaTwoFundamentalDomain) (C : ℝ) (hC : 0 ≤ C) :
    ∃ Y : ℝ, 1 ≤ Y ∧ C * energy Y < contribution D Y := by
  obtain ⟨Y, hY, h⟩ := no_bound C hC
  exact ⟨Y, hY, (contribution_eq_coordinate D Y hY).symm ▸ h⟩

end
end ManuscriptAudit.Paper9QuotientPotentialHeight

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper9QuotientPotentialHeight.contribution_eq_coordinate,
      ``ManuscriptAudit.Paper9QuotientPotentialHeight.contribution_no_bound] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
