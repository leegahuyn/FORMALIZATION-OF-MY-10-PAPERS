import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper10UnitWindowDecomposition

/-! Uniform spectral-weight envelopes yield the full real-exponent cutoff estimate. -/

namespace ManuscriptAudit.Paper10UniformTransformTail

open Paper10UnitWindowDecomposition

noncomputable section

def cutoff (T : ℝ) : ℝ := T + (Real.log T)^2

theorem every_power_tail_bound {ι : Type*} (t w : ℝ → ι → ℝ)
    (S : ℝ → ℕ → Finset ι) {C : ℝ} (hC : 0 ≤ C)
    (hWindows : ∀ T : ℝ, 1 ≤ T → ∀ (k : ℕ) (j : ι), j ∈ S T k ↔
      cutoff T + (k : ℝ) ≤ t T j ∧ t T j < cutoff T + (k : ℝ) + 1)
    (hCount : ∀ T : ℝ, 1 ≤ T → ∀ k : ℕ, ((S T k).card : ℝ) ≤ C * (1 + cutoff T + (k : ℝ)))
    (hDecay : ∀ A : ℕ, ∃ B : ℝ, 0 ≤ B ∧
      ∀ T : ℝ, 1 ≤ T → ∀ j : ι, cutoff T ≤ t T j → |w T j| ≤ B / (1+t T j)^(A+3))
    (a : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℝ, 1 ≤ T →
      Summable (fun j : {j : ι // cutoff T ≤ t T j} => |w T j.val|) ∧
      (∑' j : {j : ι // cutoff T ≤ t T j}, |w T j.val|) ≤ K * T ^ (-a) := by
  let N : ℕ := ⌈a⌉₊
  obtain ⟨B, hB, hD⟩ := hDecay N
  let M : ℝ := ∑' k : ℕ, 1 / ((k : ℝ)+1)^2
  have hM : 0 ≤ M := tsum_nonneg (fun _ => by positivity)
  let K : ℝ := C*B*M + 1
  have hK : 0 < K := by
    have h : 0 ≤ C*B*M := mul_nonneg (mul_nonneg hC hB) hM
    dsimp only [K]
    linarith
  refine ⟨K, hK, fun T hT => ?_⟩
  have hT0 : 0 < T := by linarith
  have hN : a ≤ (N : ℝ) := Nat.le_ceil _
  have hpow : T^a ≤ T^N := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hT hN
  obtain ⟨hs, hh⟩ := logarithmic_cutoff_bound (t T) (S T) (w T) T hT N hC hB
      (hWindows T hT) (hD T hT) (hCount T hT)
  refine ⟨hs, hh.trans ?_⟩
  rw [Real.rpow_neg hT0.le]
  calc
    (C*B / T^N) * M = (C*B*M) / T^N := by ring
    _ ≤ C*B*M / T^a :=
      div_le_div_of_nonneg_left (mul_nonneg (mul_nonneg hC hB) hM)
        (Real.rpow_pos_of_pos hT0 _) hpow
    _ ≤ K / T^a :=
      div_le_div_of_nonneg_right (by dsimp only [K]; linarith) (Real.rpow_nonneg hT0.le _)
    _ = K * (T^a)⁻¹ := div_eq_mul_inv _ _

end
end ManuscriptAudit.Paper10UniformTransformTail

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.Paper10UniformTransformTail.every_power_tail_bound
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
