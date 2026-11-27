import Lean.Util.CollectAxioms
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import PrimalitySheafVerification.ManuscriptAudit.Paper8AbelNormalization
import PrimalitySheafVerification.ManuscriptAudit.Paper8EvenGcdOrderedLimit

/-!
# A mode-zero obstruction for unshifted reduced denominator progressions

The arithmetic input is the nonzero square-root main term for
the sum of A_D(0)/D through a finite cutoff. Ahlgren and Andersen,
*Algebraic and transcendental formulas for the smallest parts
function*, Theorem 3 at n = 0, prove this externally with constant
12√3/π², https://arxiv.org/pdf/1504.02500 .
Our sign of the Dedekind-sum exponential is conjugate to theirs,
which leaves that real main term unchanged. The asymptotic is
an explicit hypothesis here. The conclusion concerns the unshifted
reduced denominator progression terms before the signed even-gcd
recombination.
-/

namespace ManuscriptAudit.Paper8UnshiftedZeroMode

open Filter
open scoped Topology
open Paper8ContourGammaSeries (coefficient coefficient_pos)
open Paper8AllResidueDivisorSum (reducedFrequencySum)
open Paper8OddGcdOrderedLimit (coefficient_zero_rescale)
open Paper8EvenGcdOrderedLimit (unshiftedCoefficient progressionPartialSum)
open Paper8SeparateContourSeries (orderedPartialSum)
open Paper8AbelNormalization (normalized_partial_sums_tendsto_zero)

noncomputable section

def rawTerm (j : ℕ) : ℂ :=
  reducedFrequencySum (j + 1) 0 / ((j + 1 : ℕ) : ℂ)

def squareRootScale (j : ℕ) : ℝ := Real.sqrt ((j + 1 : ℕ) : ℝ)

theorem sqrt_smul_coefficient (j : ℕ) :
    squareRootScale j • unshiftedCoefficient (j + 1) 0 =
      -(coefficient 1 0 : ℂ) * rawTerm j := by
  have hs : 0 < squareRootScale j :=
    Real.sqrt_pos.2 (Nat.cast_pos.mpr (Nat.succ_pos j))
  have hC : coefficient (j + 1) 0 = (1 / squareRootScale j) * coefficient 1 0 := by
    simpa only [Nat.mul_one, ← Real.sqrt_eq_rpow, squareRootScale] using
      coefficient_zero_rescale (Nat.succ_pos j) (Nat.succ_pos 0)
  have hsC : (squareRootScale j : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  unfold unshiftedCoefficient rawTerm
  rw [hC, Complex.real_smul, neg_zero]
  push_cast
  field_simp [hsC] <;> ring

theorem unshifted_zero_mode_has_no_ordered_limit {A : ℂ} (hA : A ≠ 0)
    (hMain : Tendsto (fun N => (squareRootScale N)⁻¹ •
      (∑ j ∈ Finset.range (N + 1), rawTerm j)) atTop (𝓝 A)) :
    ¬ ∃ L : ℂ, Tendsto
      (orderedPartialSum (fun j => unshiftedCoefficient (j + 1) 0)) atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  have hPos (j : ℕ) : 0 < squareRootScale j :=
    Real.sqrt_pos.2 (Nat.cast_pos.mpr (Nat.succ_pos j))
  have hMono : Monotone squareRootScale := by
    intro i j hij
    apply Real.sqrt_le_sqrt
    exact_mod_cast Nat.succ_le_succ hij
  have hShift : Tendsto (fun n : ℕ => n + 1) atTop atTop := by
    refine tendsto_atTop.2 fun b => (eventually_ge_atTop b).mono fun n hn => ?_
    exact hn.trans (Nat.le_succ n)
  have hScale : Tendsto squareRootScale atTop atTop := by
    simp only [squareRootScale, Real.sqrt_eq_rpow]
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hShift)
  have hz := normalized_partial_sums_tendsto_zero squareRootScale
    (fun j => unshiftedCoefficient (j + 1) 0) hPos hMono hScale hL
  have hAsymptotic : Tendsto (fun N => (squareRootScale N)⁻¹ •
      (∑ j ∈ Finset.range (N + 1), squareRootScale j • unshiftedCoefficient (j + 1) 0))
      atTop (𝓝 (-(coefficient 1 0 : ℂ) * A)) := by
    refine (tendsto_const_nhds.mul hMain).congr fun N => ?_
    simp only [sqrt_smul_coefficient, ← Finset.mul_sum, Complex.real_smul]
    ring
  have hP : (coefficient 1 0 : ℂ) ≠ 0 := by
    exact_mod_cast (coefficient_pos (Nat.succ_pos 0) 0).ne'
  exact (mul_ne_zero (neg_ne_zero.mpr hP) hA) (tendsto_nhds_unique hAsymptotic hz)

theorem four_unweighted_progression_limits_impossible {A : ℂ} (hA : A ≠ 0)
    (hMain : Tendsto (fun N => (squareRootScale N)⁻¹ •
      (∑ j ∈ Finset.range (N + 1), rawTerm j)) atTop (𝓝 A)) :
    ¬ ∃ L : ℕ → ℂ, ∀ r ∈ Finset.range 4,
      Tendsto (progressionPartialSum (fun D => unshiftedCoefficient D 0) r) atTop (𝓝 (L r)) := by
  rintro ⟨L, hL⟩
  have hLim := tendsto_finsetSum (Finset.range 4) hL
  refine unshifted_zero_mode_has_no_ordered_limit hA hMain ⟨_, hLim.congr fun N => ?_⟩
  simp only [progressionPartialSum, orderedPartialSum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_eq_single_of_mem ((d + 1) % 4)
    (Finset.mem_range.mpr (Nat.mod_lt _ (by decide))) (fun r _ h => by
      simp only [if_neg (Ne.symm h)]), if_pos rfl]

end
end ManuscriptAudit.Paper8UnshiftedZeroMode

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8UnshiftedZeroMode.sqrt_smul_coefficient,
      ``ManuscriptAudit.Paper8UnshiftedZeroMode.unshifted_zero_mode_has_no_ordered_limit,
      ``ManuscriptAudit.Paper8UnshiftedZeroMode.four_unweighted_progression_limits_impossible] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
