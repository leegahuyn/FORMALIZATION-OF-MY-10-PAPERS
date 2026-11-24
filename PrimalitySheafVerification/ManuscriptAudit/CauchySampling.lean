import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# The finite Laurent version of the Cauchy sample

Paper 8, physical PDF p. 350, evaluates a circle integral by equidistant
samples. For a Laurent polynomial the sampled coefficient has an exact
formula. It includes every exponent congruent to the target modulo the
number of nodes. The same identity extends to an absolutely convergent
Laurent series on the sampling circle.
-/

open scoped BigOperators

namespace ManuscriptAudit.CauchySampling

noncomputable def finiteLaurent (s : Finset ℤ) (a : ℤ → ℂ) (q : ℂ) : ℂ :=
  ∑ k ∈ s, a k * q ^ k

private theorem zpow_nat_comm (z : ℂ) (j : ℕ) (d : ℤ) :
    (z ^ j) ^ d = (z ^ d) ^ j := by
  simpa only [zpow_natCast] using zpow_comm z (j : ℤ) d

private theorem sum_grid_character {M : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ M) (d : ℤ) :
    (∑ j ∈ Finset.range M, (ζ ^ d) ^ j) = if (M : ℤ) ∣ d then (M : ℂ) else 0 := by
  by_cases hd : (M : ℤ) ∣ d
  · simp [(hζ.zpow_eq_one_iff_dvd d).2 hd, hd]
  · have hne : ζ ^ d ≠ 1 := fun h => hd ((hζ.zpow_eq_one_iff_dvd d).1 h)
    rw [if_neg hd, geom_sum_eq hne, ← zpow_nat_comm ζ M d, hζ.pow_eq_one,
      one_zpow, sub_self, zero_div]

private theorem sample_powers (M j : ℕ) :
    (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (M : ℂ))) ^ j =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) / (M : ℂ)) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

private theorem sample_neg_power (r : ℂ) (M j : ℕ) (n : ℤ) :
    (r * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (M : ℂ))) ^ j) ^ (-n) =
      r ^ (-n) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (j : ℂ) / (M : ℂ))) := by
  rw [mul_zpow, sample_powers, ← Complex.exp_int_mul]
  apply congrArg (fun z : ℂ => r ^ (-n) * z)
  congr 1
  simp only [Int.cast_neg]
  ring

/-- Exact discrete sampling at the `M` equidistant nodes of a nonzero circle. -/
theorem finiteLaurent_sample_eq (s : Finset ℤ) (a : ℤ → ℂ) (r : ℂ)
    (hr : r ≠ 0) (M : ℕ) (hM : M ≠ 0) (n : ℤ) :
    let ζ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (M : ℂ))
    (M : ℂ)⁻¹ *
        (∑ j ∈ Finset.range M, finiteLaurent s a (r * ζ ^ j) * (r * ζ ^ j) ^ (-n)) =
      ∑ k ∈ s.filter (fun k => (M : ℤ) ∣ k - n), a k * r ^ (k - n) := by
  let ζ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (M : ℂ))
  change (M : ℂ)⁻¹ *
      (∑ j ∈ Finset.range M, finiteLaurent s a (r * ζ ^ j) * (r * ζ ^ j) ^ (-n)) =
    ∑ k ∈ s.filter (fun k => (M : ℤ) ∣ k - n), a k * r ^ (k - n)
  have hζ : IsPrimitiveRoot ζ M := Complex.isPrimitiveRoot_exp M hM
  have hM' : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM
  have hexpand :
      (∑ j ∈ Finset.range M, finiteLaurent s a (r * ζ ^ j) * (r * ζ ^ j) ^ (-n)) =
        ∑ k ∈ s, a k * r ^ (k - n) * (if (M : ℤ) ∣ k - n then (M : ℂ) else 0) := by
    calc
      _ = ∑ j ∈ Finset.range M, ∑ k ∈ s, a k * r ^ (k - n) * (ζ ^ (k - n)) ^ j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        have hnode : r * ζ ^ j ≠ 0 := mul_ne_zero hr (pow_ne_zero _ (hζ.ne_zero hM))
        rw [finiteLaurent, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [mul_assoc, ← zpow_add₀ hnode, ← sub_eq_add_neg, mul_zpow, zpow_nat_comm,
          ← mul_assoc]
      _ = ∑ k ∈ s, ∑ j ∈ Finset.range M, a k * r ^ (k - n) * (ζ ^ (k - n)) ^ j :=
        Finset.sum_comm
      _ = _ := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← Finset.mul_sum, sum_grid_character hζ]
  rw [hexpand, Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : (M : ℤ) ∣ k - n
  · simp only [if_pos hk]
    calc
      _ = ((M : ℂ)⁻¹ * (M : ℂ)) * (a k * r ^ (k - n)) := by ring
      _ = _ := by rw [inv_mul_cancel₀ hM', one_mul]
  · simp [hk]

/-- The same exact identity written using the two exponential phases on p. 350. -/
theorem finiteLaurent_printed_sample_eq (s : Finset ℤ) (a : ℤ → ℂ) (r : ℂ)
    (hr : r ≠ 0) (M : ℕ) (hM : M ≠ 0) (n : ℤ) :
    (M : ℂ)⁻¹ * (∑ j ∈ Finset.range M,
      finiteLaurent s a (r * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) / (M : ℂ))) *
        (r ^ (-n) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (j : ℂ) / (M : ℂ))))) =
      ∑ k ∈ s.filter (fun k => (M : ℤ) ∣ k - n), a k * r ^ (k - n) := by
  rw [← finiteLaurent_sample_eq s a r hr M hM n]
  apply congrArg (fun z : ℂ => (M : ℂ)⁻¹ * z)
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sample_neg_power, sample_powers]

/-- The coefficient reported at zero for the monomial `q^M` is `r^M`. -/
theorem sample_monomial_at_zero (r : ℂ) (hr : r ≠ 0) (M : ℕ) (hM : M ≠ 0) :
    (M : ℂ)⁻¹ * (∑ j ∈ Finset.range M,
      (r * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) / (M : ℂ))) ^ M) = r ^ M := by
  simpa only [finiteLaurent, Finset.sum_filter, Finset.sum_singleton, zpow_natCast,
    Int.cast_zero, neg_zero, zpow_zero, mul_zero, zero_mul, zero_div, Complex.exp_zero,
    sub_zero, dvd_refl, if_true, one_mul, mul_one] using
      finiteLaurent_printed_sample_eq {(M : ℤ)} (fun _ => 1) r hr M hM 0

/-- Absolute convergence at one nonzero radius gives the exact sampled
Laurent coefficient as an absolutely justified alias sum. Each node series
and the displayed alias series are summable. -/
theorem absoluteLaurent_sample_eq (a : ℤ → ℂ) (r : ℂ) (hr : r ≠ 0)
    (M : ℕ) (hM : M ≠ 0) (n : ℤ) (hAbs : Summable (fun k : ℤ => ‖a k * r ^ k‖)) :
    let ζ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (M : ℂ))
    (∀ j : ℕ, Summable (fun k : ℤ => a k * (r * ζ ^ j) ^ k)) ∧
    Summable (fun k : ℤ => if (M : ℤ) ∣ k - n then a k * r ^ (k - n) else 0) ∧
    (M : ℂ)⁻¹ * (∑ j ∈ Finset.range M,
      (∑' k : ℤ, a k * (r * ζ ^ j) ^ k) * (r * ζ ^ j) ^ (-n)) =
        ∑' k : ℤ, if (M : ℤ) ∣ k - n then a k * r ^ (k - n) else 0 := by
  let ζ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (M : ℂ))
  change (∀ j : ℕ, Summable (fun k : ℤ => a k * (r * ζ ^ j) ^ k)) ∧
    Summable (fun k : ℤ => if (M : ℤ) ∣ k - n then a k * r ^ (k - n) else 0) ∧
    (M : ℂ)⁻¹ * (∑ j ∈ Finset.range M,
      (∑' k : ℤ, a k * (r * ζ ^ j) ^ k) * (r * ζ ^ j) ^ (-n)) =
        ∑' k : ℤ, if (M : ℤ) ∣ k - n then a k * r ^ (k - n) else 0
  have hζ : IsPrimitiveRoot ζ M := Complex.isPrimitiveRoot_exp M hM
  have hM' : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM
  have hNode (j : ℕ) : Summable (fun k : ℤ => a k * (r * ζ ^ j) ^ k) := by
    refine hAbs.of_norm_bounded fun k => ?_
    simp only [norm_mul, norm_zpow, norm_pow, hζ.norm'_eq_one hM, one_pow, mul_one, le_refl]
  let weighted (j : ℕ) (k : ℤ) : ℂ :=
    (M : ℂ)⁻¹ * ((a k * (r * ζ ^ j) ^ k) * (r * ζ ^ j) ^ (-n))
  have hWeighted (j : ℕ) : Summable (weighted j) :=
    ((hNode j).mul_right ((r * ζ ^ j) ^ (-n))).mul_left ((M : ℂ)⁻¹)
  have hGrid (k : ℤ) :
      (∑ j ∈ Finset.range M, weighted j k) =
        if (M : ℤ) ∣ k - n then a k * r ^ (k - n) else 0 := by
    have hTerm (j : ℕ) : weighted j k =
        ((M : ℂ)⁻¹ * (a k * r ^ (k - n))) * (ζ ^ (k - n)) ^ j := by
      have hq : r * ζ ^ j ≠ 0 := mul_ne_zero hr (pow_ne_zero _ (hζ.ne_zero hM))
      dsimp only [weighted]
      rw [mul_assoc (a k), ← zpow_add₀ hq, ← sub_eq_add_neg, mul_zpow, zpow_nat_comm]
      ring
    simp_rw [hTerm]
    rw [← Finset.mul_sum, sum_grid_character hζ]
    by_cases hk : (M : ℤ) ∣ k - n
    · simp only [if_pos hk]
      calc
        _ = ((M : ℂ)⁻¹ * (M : ℂ)) * (a k * r ^ (k - n)) := by ring
        _ = _ := by rw [inv_mul_cancel₀ hM', one_mul]
    · simp [hk]
  have hInterchange :
      HasSum (fun k : ℤ => ∑ j ∈ Finset.range M, weighted j k)
        (∑ j ∈ Finset.range M, ∑' k : ℤ, weighted j k) :=
    hasSum_sum fun j _ => (hWeighted j).hasSum
  refine ⟨hNode, ?_, ?_⟩
  · simpa only [hGrid] using hInterchange.summable
  · rw [Finset.mul_sum]
    calc
      _ = ∑ j ∈ Finset.range M, ∑' k : ℤ, weighted j k := by
        refine Finset.sum_congr rfl fun j _ => ?_
        dsimp only [weighted]
        rw [tsum_mul_left, tsum_mul_right]
      _ = ∑' k : ℤ, ∑ j ∈ Finset.range M, weighted j k := hInterchange.tsum_eq.symm
      _ = _ := tsum_congr hGrid

end ManuscriptAudit.CauchySampling

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
    ``ManuscriptAudit.CauchySampling.finiteLaurent_sample_eq,
    ``ManuscriptAudit.CauchySampling.finiteLaurent_printed_sample_eq,
    ``ManuscriptAudit.CauchySampling.sample_monomial_at_zero,
    ``ManuscriptAudit.CauchySampling.absoluteLaurent_sample_eq] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
