import Lean.Util.CollectAxioms
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Pi.Bounds

/-! A quantitative small-argument decay condition that suffices for the absolute modulus sum. -/

namespace ManuscriptAudit.Paper9KloostermanConvergence

open Filter

noncomputable section

/-- The size estimate of pp. 431–432 does give absolute summability for each
fixed positive diagonal index once the kernel vanishes at zero with the
indicated power. This theorem is about the stated estimates. -/
theorem diagonal_absolutely_summable_of_small_argument_decay (m : ℕ) (hm : 0 < m)
    (coeff : ℕ → ℂ) (kernel : ℝ → ℂ) {C D ε r : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hr : 1 / 2 + ε < r)
    (hCoeff : ∀ c : ℕ, 0 < c →
      ‖coeff c‖ ≤ C * (c : ℝ) ^ (1 / 2 + ε) * Real.sqrt (Nat.gcd m c))
    (hKernel : ∀ x : ℝ, 0 < x → x ≤ 1 → ‖kernel x‖ ≤ D * x ^ r) :
    Summable (fun n : ℕ => ‖coeff (n + 1) / ((n + 1 : ℕ) : ℂ) *
      kernel (4 * Real.pi * (m : ℝ) / ((n + 1 : ℕ) : ℝ))‖) := by
  let A : ℝ := 4 * Real.pi * (m : ℝ)
  let p : ℝ := 1 / 2 + ε
  let K : ℝ := C * D * Real.sqrt m * A ^ r
  have hA : 0 < A := by
    have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
    unfold A
    positivity
  have hs : p - 1 - r < -1 := by
    change 1 / 2 + ε - 1 - r < -1
    linarith
  have hMajorant : Summable (fun n : ℕ => K * (((n + 1 : ℕ) : ℝ) ^ (p - 1 - r))) :=
    ((summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 hs)).mul_left K
  refine hMajorant.of_norm_bounded_eventually_nat ?_
  rcases exists_nat_gt A with ⟨N, hN⟩
  filter_upwards [eventually_ge_atTop N] with n hn
  let c := n + 1
  have hc : 0 < c := Nat.succ_pos n
  have hcR : 0 < (c : ℝ) := by exact_mod_cast hc
  have hcC : ‖(c : ℂ)‖ = (c : ℝ) := by
    rw [← Complex.ofReal_natCast, Complex.norm_real, Real.norm_of_nonneg (Nat.cast_nonneg _)]
  have hAc : A ≤ (c : ℝ) := by
    have hNat : N ≤ c := hn.trans (Nat.le_succ n)
    exact hN.le.trans (by exact_mod_cast hNat)
  have hx : 0 < A / (c : ℝ) := div_pos hA hcR
  have hx1 : A / (c : ℝ) ≤ 1 := (div_le_one₀ hcR).2 hAc
  have hGcd : Real.sqrt (Nat.gcd m c) ≤ Real.sqrt m := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast Nat.le_of_dvd hm (Nat.gcd_dvd_left m c)
  have hCoef : ‖coeff c‖ ≤ C * (c : ℝ) ^ p * Real.sqrt m :=
    (hCoeff c hc).trans (mul_le_mul_of_nonneg_left hGcd
      (mul_nonneg hC (Real.rpow_nonneg hcR.le _)))
  have hKer := hKernel (A / (c : ℝ)) hx hx1
  have hPow : (c : ℝ) ^ (p - 1 - r) = ((c : ℝ) ^ p / (c : ℝ)) / (c : ℝ) ^ r := by
    rw [Real.rpow_sub hcR, Real.rpow_sub hcR, Real.rpow_one]
  change ‖‖coeff c / (c : ℂ) * kernel (A / (c : ℝ))‖‖ ≤ K * (c : ℝ) ^ (p - 1 - r)
  rw [Real.norm_of_nonneg (norm_nonneg _), norm_mul, norm_div, hcC]
  calc
    _ ≤ (C * (c : ℝ) ^ p * Real.sqrt m / (c : ℝ)) * (D * (A / (c : ℝ)) ^ r) :=
      mul_le_mul (div_le_div_of_nonneg_right hCoef hcR.le) hKer (norm_nonneg _)
        (div_nonneg (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hcR.le _)) (Real.sqrt_nonneg _)) hcR.le)
    _ = _ := by
      rw [Real.div_rpow hA.le hcR.le, hPow]
      unfold K
      ring

end
end ManuscriptAudit.Paper9KloostermanConvergence

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper9KloostermanConvergence.diagonal_absolutely_summable_of_small_argument_decay
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← collectAxioms name
  let bad := axioms.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {axioms}"
