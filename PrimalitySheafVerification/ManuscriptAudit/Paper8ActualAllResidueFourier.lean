import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8AllResidueDivisorSum
import PrimalitySheafVerification.ManuscriptAudit.Paper8ReciprocalArithmeticRows

/-! The actual all-residue lower contour coefficient is a finite divisor sum at its shifted frequency. -/

namespace ManuscriptAudit.Paper8ActualAllResidueFourier

open Paper8GcdArithmeticWeight Paper8AllResidueDivisorSum Paper8ReciprocalCommonFourier
open Paper8ReciprocalArithmeticRows
open Paper8ContourGammaSeries (coefficient)
open Paper8ContourResidueWeights (prefactor)

theorem all_arithmetic_row_divisor_sum {k : ℕ} (hk : 0 < k) (u : ℝ) :
    arithmeticSum (fun _ => Finset.univ) k u =
      ∑ g ∈ (2*k).divisors, reducedFrequencySum ((2*k)/g) u := by
  have h : arithmeticSum (fun _ => Finset.univ) k u =
      ∑ d : Fin (2*k), frequencyWeight (2*k) u d := by
    unfold arithmeticSum
    apply Finset.sum_congr rfl
    intro d _
    unfold frequencyWeight
    rw [Nat.cast_mul, Nat.cast_ofNat]
  rw [h]
  exact all_frequency_sum_eq_divisor_sum (by omega : 0 < 2*k) u

theorem all_fourier_row_divisor_sum {k : ℕ} (hk : 0 < k) (n : ℕ) :
    fourierCoefficient (fun _ => Finset.univ) k n =
      -prefactor k * ((coefficient k 0 : ℂ) *
        ∑ g ∈ (2*k).divisors, reducedFrequencySum ((2*k)/g) (shiftedFrequency k n)) := by
  rw [fourierCoefficient_eq_arithmeticSum _ hk n, all_arithmetic_row_divisor_sum hk]

end ManuscriptAudit.Paper8ActualAllResidueFourier

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ActualAllResidueFourier.all_arithmetic_row_divisor_sum,
      ``ManuscriptAudit.Paper8ActualAllResidueFourier.all_fourier_row_divisor_sum] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
