import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8UnshiftedZeroMode

/-! A fixed even-gcd mode-zero obstruction under the Ahlgren–Andersen input. -/

namespace ManuscriptAudit.Paper8FixedHalfGcdZero

open Filter
open scoped Topology
open Paper8ContourGammaSeries (coefficient)
open Paper8ContourResidueWeights (prefactor)
open Paper8ReciprocalArithmeticRows (shiftedFrequency)
open Paper8AllResidueDivisorSum (reducedFrequencySum)
open Paper8OddGcdResiduePhase (modulusSign)
open Paper8EvenGcdArithmeticRows (evenGcdSign sign_depends_on_mod_four
  even_residue_class_fourier_rescale)
open Paper8EvenGcdOrderedLimit (unshiftedCoefficient)
open Paper8SeparateContourSeries (orderedPartialSum)
open Paper8UnshiftedZeroMode (squareRootScale rawTerm unshifted_zero_mode_has_no_ordered_limit)

noncomputable section

theorem evenGcdSign_eq_one_of_four_dvd {h : ℕ} (hh : 4 ∣ h) (D : ℕ) :
    evenGcdSign h D = 1 := by
  rw [sign_depends_on_mod_four h D, Nat.mod_eq_zero_of_dvd hh]
  simp [evenGcdSign, modulusSign]

def halfGcdClass (h D : ℕ) : ℂ :=
  -prefactor (h * D) * ((coefficient (h * D) 0 : ℂ) *
    reducedFrequencySum D (shiftedFrequency (h * D) 0))

/-- This is a fixed half-gcd subseries in D of the literal even sector. -/
theorem fixed_half_gcd_zero_mode_has_no_ordered_limit {h : ℕ} (hh : 0 < h)
    (hh4 : 4 ∣ h) {A : ℂ} (hA : A ≠ 0)
    (hMain : Tendsto (fun N => (squareRootScale N)⁻¹ •
      (∑ j ∈ Finset.range (N + 1), rawTerm j)) atTop (𝓝 A)) :
    ¬ ∃ L : ℂ, Tendsto (orderedPartialSum (fun j => halfGcdClass h (j + 1))) atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  let c : ℂ := ((1 / (h : ℝ) ^ (3 / 2 : ℝ) : ℝ) : ℂ)
  have hR : 0 < (h : ℝ) := by exact_mod_cast hh
  have hC : c ≠ 0 := by
    have hPos : 0 < 1 / (h : ℝ) ^ (3 / 2 : ℝ) :=
      div_pos zero_lt_one (Real.rpow_pos_of_pos hR _)
    exact Complex.ofReal_ne_zero.mpr hPos.ne'
  have hClass (j : ℕ) : halfGcdClass h (j + 1) = c * unshiftedCoefficient (j + 1) 0 := by
    unfold halfGcdClass
    rw [even_residue_class_fourier_rescale hh (Nat.succ_pos j) 0,
      evenGcdSign_eq_one_of_four_dvd hh4, mul_one]
    rfl
  have hSum (N : ℕ) : orderedPartialSum (fun j => halfGcdClass h (j + 1)) N =
      c * orderedPartialSum (fun j => unshiftedCoefficient (j + 1) 0) N := by
    unfold orderedPartialSum
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => hClass j)
  apply unshifted_zero_mode_has_no_ordered_limit hA hMain
  refine ⟨c⁻¹ * L, (tendsto_const_nhds.mul hL).congr fun N => ?_⟩
  change c⁻¹ * orderedPartialSum (fun j => halfGcdClass h (j + 1)) N = _
  rw [hSum, ← mul_assoc, inv_mul_cancel₀ hC, one_mul]

end
end ManuscriptAudit.Paper8FixedHalfGcdZero

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8FixedHalfGcdZero.evenGcdSign_eq_one_of_four_dvd,
      ``ManuscriptAudit.Paper8FixedHalfGcdZero.fixed_half_gcd_zero_mode_has_no_ordered_limit] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
