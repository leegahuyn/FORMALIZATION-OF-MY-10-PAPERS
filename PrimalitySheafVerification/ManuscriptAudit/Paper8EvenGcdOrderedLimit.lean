import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8EvenGcdArithmeticRows

/-!
# Ordinary even-gcd limits from four reduced denominator progressions

At a fixed reciprocal Fourier mode, the even gcd classes require
unshifted reduced-modulus sums. Their weights depend on the reduced
denominator modulo four and decay in the half-gcd as h^(-3/2).
The checked odd-sector convergence argument then applies separately
to each of the four progressions, given its ordinary cutoff limit.
-/

namespace ManuscriptAudit.Paper8EvenGcdOrderedLimit

open Filter
open scoped Topology
open Paper8ContourResidueWeights (prefactor)
open Paper8ContourGammaSeries (coefficient)
open Paper8ReciprocalArithmeticRows (shiftedFrequency)
open Paper8AllResidueDivisorSum (reducedFrequencySum)
open Paper8SeparateContourSeries (orderedPartialSum)
open Paper8OddGcdOrderedLimit (weighted_divided_partial_limits)
open Paper8OddGcdResiduePhase (modulusSign)
open Paper8EvenGcdArithmeticRows (evenGcdSign sign_depends_on_mod_four
  even_residue_class_fourier_rescale)

noncomputable section

def evenWeight (h D : ℕ) : ℂ :=
  ((1 / (h : ℝ) ^ (3 / 2 : ℝ) : ℝ) : ℂ) * evenGcdSign h D

private theorem evenWeight_reduces_second (h D : ℕ) :
    evenWeight h D = evenWeight h (D % 4) := by
  unfold evenWeight
  congr 1
  calc
    evenGcdSign h D = evenGcdSign (h % 4) (D % 4) := sign_depends_on_mod_four h D
    _ = evenGcdSign h (D % 4) := by
      rw [sign_depends_on_mod_four h (D % 4), Nat.mod_mod]

theorem evenWeight_norm (h D : ℕ) : ‖evenWeight h D‖ = 1 / (h : ℝ) ^ (3 / 2 : ℝ) := by
  have hs : ‖evenGcdSign h D‖ = 1 := by
    unfold evenGcdSign
    split_ifs <;> simp [modulusSign]
  rw [evenWeight, norm_mul, hs, mul_one, Complex.norm_real, Real.norm_of_nonneg (by positivity)]

theorem evenWeight_norm_summable (r : ℕ) : Summable (fun h : ℕ => ‖evenWeight (h + 1) r‖) := by
  simp only [evenWeight_norm]
  exact (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_rpow.2 (by norm_num))

def progressionPartialSum (f : ℕ → ℂ) (r : ℕ) : ℕ → ℂ :=
  orderedPartialSum (fun d => if (d + 1) % 4 = r then f (d + 1) else 0)

theorem progressions_recombine (f : ℕ → ℂ) (h M : ℕ) :
    (∑ r ∈ Finset.range 4, evenWeight h r * progressionPartialSum f r M) =
      ∑ d ∈ Finset.range M, evenWeight h (d + 1) * f (d + 1) := by
  simp only [progressionPartialSum, orderedPartialSum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_eq_single_of_mem ((d + 1) % 4)
    (Finset.mem_range.mpr (Nat.mod_lt _ (by decide))) (fun r _ h => by
      simp only [if_neg (Ne.symm h), mul_zero])]
  rw [if_pos rfl, ← evenWeight_reduces_second]

private theorem divided_sum_eq_finite (f : ℕ → ℂ) (r N : ℕ) :
    (∑' h : ℕ, evenWeight (h + 1) r * progressionPartialSum f r (N / (h + 1))) =
      ∑ h ∈ Finset.range N, evenWeight (h + 1) r * progressionPartialSum f r (N / (h + 1)) := by
  apply tsum_eq_sum
  intro h hh
  have hle : N ≤ h := by simpa only [Finset.mem_range, not_lt] using hh
  rw [Nat.div_eq_of_lt (Nat.lt_succ_of_le hle), progressionPartialSum, orderedPartialSum,
    Finset.range_zero, Finset.sum_empty, mul_zero]

def unshiftedCoefficient (D n : ℕ) : ℂ :=
  -((coefficient D 0 : ℂ) / (D : ℂ)) * reducedFrequencySum D (-(n : ℝ))

/-- All pairs of positive half-gcd and denominator with product at most the cutoff. -/
def evenSectorCutoff (N n : ℕ) : ℂ :=
  ∑ h ∈ Finset.range N, ∑ d ∈ Finset.range (N / (h + 1)),
    (-prefactor ((h + 1) * (d + 1))) *
      ((coefficient ((h + 1) * (d + 1)) 0 : ℂ) *
        reducedFrequencySum (d + 1) (shiftedFrequency ((h + 1) * (d + 1)) n))

theorem evenSectorCutoff_eq_progressions (N n : ℕ) :
    evenSectorCutoff N n = ∑ r ∈ Finset.range 4,
      ∑' h : ℕ, evenWeight (h + 1) r *
        progressionPartialSum (fun D => unshiftedCoefficient D n) r (N / (h + 1)) := by
  simp only [divided_sum_eq_finite]
  rw [Finset.sum_comm]
  unfold evenSectorCutoff
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [progressions_recombine]
  refine Finset.sum_congr rfl fun d _ => ?_
  exact even_residue_class_fourier_rescale (Nat.succ_pos h) (Nat.succ_pos d) n

theorem even_sector_limit_of_progressions (n : ℕ) (L : ℕ → ℂ)
    (hL : ∀ r ∈ Finset.range 4,
      Tendsto (progressionPartialSum (fun D => unshiftedCoefficient D n) r) atTop (𝓝 (L r))) :
    Tendsto (fun N => evenSectorCutoff N n) atTop
      (𝓝 (∑ r ∈ Finset.range 4, ∑' h : ℕ, evenWeight (h + 1) r * L r)) := by
  have h := tendsto_finsetSum (Finset.range 4) (fun r hr =>
    weighted_divided_partial_limits
      (progressionPartialSum (fun D => unshiftedCoefficient D n) r)
      (fun h => evenWeight (h + 1) r) (hL r hr) (evenWeight_norm_summable r))
  exact h.congr fun N => (evenSectorCutoff_eq_progressions N n).symm

end
end ManuscriptAudit.Paper8EvenGcdOrderedLimit

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8EvenGcdOrderedLimit.evenWeight_norm_summable,
      ``ManuscriptAudit.Paper8EvenGcdOrderedLimit.progressions_recombine,
      ``ManuscriptAudit.Paper8EvenGcdOrderedLimit.evenSectorCutoff_eq_progressions,
      ``ManuscriptAudit.Paper8EvenGcdOrderedLimit.even_sector_limit_of_progressions] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
