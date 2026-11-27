import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.GammaTwoQuotientHeightIntegral
import PrimalitySheafVerification.ManuscriptAudit.Paper9PrintedFactorizations
import PrimalitySheafVerification.ManuscriptAudit.Paper9QuotientPotentialHeight

/-! The printed three-term graph integral for the actual compact theta sections. -/

namespace ManuscriptAudit.Paper9QuotientGraphEnergy

open Set MeasureTheory GammaTwoQuotientHeightIntegral
open Paper9CuspPotentialForm Paper9CuspNormOnQuotient Paper9HighCuspCoordinates
open Paper9HighCuspSection Paper9HighCuspNegative Paper9PrintedFactorizations
open Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry
open scoped UpperHalfPlane Topology

noncomputable section

def realDensity (Y y : ℝ) : ℝ :=
  (heightTest Y y / y) ^ 2 +
    (deriv (heightTest Y) y / y + heightTest Y y / (2 * y ^ 2)) ^ 2 +
    (y * deriv (heightTest Y) y) ^ 2

def quotientDensity (Y : ℝ) (q : GammaTwoQuotient) : ℝ :=
  quotientHeight q ^ 2 * realDensity Y (quotientHeight q)

def quotientEnergy (D : GammaTwoFundamentalDomain) (Y : ℝ) : ℝ :=
  ∫ q, quotientDensity Y q ∂D.quotientMeasure

theorem quotientDensity_high (Y : ℝ) (z : ℍ) (hz : 1 < z.im) :
    quotientDensity Y (gammaTwoQuotientMk z) =
      ‖extendedSection (heightAmplitude Y) z‖ ^ (2 : ℕ) +
      ‖raise (1 / 2) (coordinates (heightAmplitude Y)) z.re z.im‖ ^ (2 : ℕ) +
      ‖lower (coordinates (heightAmplitude Y)) z.re z.im‖ ^ (2 : ℕ) := by
  let y := z.im
  let a := heightTest Y y
  let d := deriv (heightTest Y) y
  have hVal : extendedSection (heightAmplitude Y) z = (a : ℂ) :=
    extendedSection_at_high _ z hz
  have hDerivative : deriv (heightAmplitude Y) y = (d : ℂ) := by
    simp [d, heightAmplitude_deriv, heightTest_deriv]
  have hUpper : raise (1 / 2) (coordinates (heightAmplitude Y)) z.re z.im =
      ((d + a / (2 * y) : ℝ) : ℂ) := by
    rw [raise_high _ _ _ _ hz, hDerivative]
    change (d : ℂ) + ((↑((1 / 2 : ℝ))) : ℂ) / (y : ℂ) * (a : ℂ) =
      ((d + a / (2 * y) : ℝ) : ℂ)
    push_cast
    have hy : (y : ℂ) ≠ 0 := by exact_mod_cast z.im_ne_zero
    field_simp [hy] <;> ring
  have hLower : lower (coordinates (heightAmplitude Y)) z.re z.im =
      ((y ^ 2 * d : ℝ) : ℂ) := by
    rw [lower_high _ _ _ hz, hDerivative]
    push_cast
  rw [quotientDensity, quotientHeight_high z hz.le, hVal, hUpper, hLower]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  change y ^ 2 * ((a / y) ^ 2 + (d / y + a / (2 * y ^ 2)) ^ 2 + (y * d) ^ 2) = _
  have hy : y ≠ 0 := z.im_ne_zero
  field_simp [hy] <;> ring

private theorem derivative_zero (Y y : ℝ) (hy : y < Y + 2 ∨ Y + 5 < y) :
    deriv (heightTest Y) y = 0 := by
  have h : heightTest Y =ᶠ[𝓝 y] (fun _ : ℝ => (0 : ℝ)) := by
    rcases hy with hy | hy
    · filter_upwards [Iio_mem_nhds hy] with t ht
      exact heightTest_zero Y t (Or.inl (le_of_lt ht))
    · filter_upwards [Ioi_mem_nhds hy] with t ht
      exact heightTest_zero Y t (Or.inr (le_of_lt ht))
  simpa only [deriv_const] using h.deriv_eq

private theorem realDensity_zero (Y y : ℝ) (hy : y < Y + 2 ∨ Y + 5 < y) :
    realDensity Y y = 0 := by
  rw [realDensity, heightTest_zero Y y (hy.imp le_of_lt le_of_lt), derivative_zero Y y hy]
  simp

private theorem realDensity_measurable (Y : ℝ) : Measurable (realDensity Y) := by
  have ha := (heightTest_smooth Y).continuous.measurable
  have hd := ((contDiff_infty.mp (heightTest_smooth Y) 1).continuous_deriv_one).measurable
  unfold realDensity
  fun_prop

theorem quotientDensity_zero_outside_high (Y : ℝ) (hY : 1 ≤ Y) {q : GammaTwoQuotient}
    (hq : q ∉ gammaTwoQuotientMk '' GammaTwoHighStripMeasure.strip) : quotientDensity Y q = 0 := by
  have h : quotientHeight q ≤ 1 := le_of_not_gt (fun h => hq (mem_strip_image_of_height h))
  rw [quotientDensity, realDensity_zero Y _ (Or.inl (by linarith)), mul_zero]

private theorem integral_realDensity_eq (Y : ℝ) (hY : 1 ≤ Y) :
    (∫ y in Ioi (1 : ℝ), realDensity Y y) =
      ∫ t : ℝ in (1 : ℝ)..6, energyDensity Y t := by
  let f := realDensity Y
  let A := Ioc (Y + 1) (Y + 6)
  have hA : MeasurableSet A := measurableSet_Ioc
  have hSub : A ⊆ Ioi (1 : ℝ) := by
    intro y hy
    exact lt_of_le_of_lt (by linarith) hy.1
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
        by_cases hlo : Y + 1 < y
        · have hhi : Y + 6 < y := lt_of_not_ge (fun h => hy ⟨hlo, h⟩)
          exact realDensity_zero Y y (Or.inr (by linarith))
        · have hlo' : y ≤ Y + 1 := le_of_not_gt hlo
          exact realDensity_zero Y y (Or.inl (by linarith))
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
      simp only [f, realDensity, energyDensity, heightTest_deriv, heightTest, add_sub_cancel_left]

theorem quotientEnergy_eq (D : GammaTwoFundamentalDomain) (Y : ℝ) (hY : 1 ≤ Y) :
    quotientEnergy D Y = energy Y := by
  unfold quotientEnergy quotientDensity energy
  rw [integral_profile D (realDensity Y) (realDensity_measurable Y)
      (fun y hy => realDensity_zero Y y (Or.inl (by linarith))),
    integral_realDensity_eq Y hY]

theorem quotient_potential_no_graph_bound (D : GammaTwoFundamentalDomain) (C : ℝ) (hC : 0 ≤ C) :
    ∃ Y : ℝ, 1 ≤ Y ∧ C * quotientEnergy D Y < Paper9QuotientTestPotential.contribution D Y := by
  obtain ⟨Y, hY, h⟩ := Paper9QuotientPotentialHeight.contribution_no_bound D C hC
  exact ⟨Y, hY, by simpa only [quotientEnergy_eq D Y hY] using h⟩

end
end ManuscriptAudit.Paper9QuotientGraphEnergy

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper9QuotientGraphEnergy.quotientDensity_high,
      ``ManuscriptAudit.Paper9QuotientGraphEnergy.quotientDensity_zero_outside_high,
      ``ManuscriptAudit.Paper9QuotientGraphEnergy.quotientEnergy_eq,
      ``ManuscriptAudit.Paper9QuotientGraphEnergy.quotient_potential_no_graph_bound] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
