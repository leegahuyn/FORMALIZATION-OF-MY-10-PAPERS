import Lean.Util.CollectAxioms
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.MetricSpace.Cauchy
import PrimalitySheafVerification.ManuscriptAudit.Paper10RelativeFormBounds

/-! Completeness of the shifted form metric under the actual two-sided relative form bound. -/

namespace ManuscriptAudit.Paper10RelativeFormClosed

open Filter Topology

private theorem complete_of_distance_comparison {E F : Type*}
    [PseudoMetricSpace E] [CompleteSpace E] [PseudoMetricSpace F]
    (e : F ≃ E) (c C : ℝ) (hc : 0 < c) (hC : 0 < C)
    (h₁ : ∀ x y, c * dist (e x) (e y) ≤ dist x y)
    (h₂ : ∀ x y, dist x y ≤ C * dist (e x) (e y)) : CompleteSpace F := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  have hv : CauchySeq (e ∘ u) := by
    rw [Metric.cauchySeq_iff] at hu ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hu (c * ε) (mul_pos hc hε)
    refine ⟨N, fun m hm n hn => ?_⟩
    exact (lt_of_mul_lt_mul_left ((h₁ _ _).trans_lt (hN m hm n hn)) hc.le)
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hv
  refine ⟨e.symm y, Metric.tendsto_atTop.mpr ?_⟩
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hy (ε / C) (div_pos hε hC)
  refine ⟨N, fun n hn => ?_⟩
  have hn' : dist (e (u n)) y < ε / C := hN n hn
  calc
    _ ≤ C * dist (e (u n)) (e (e.symm y)) := h₂ _ _
    _ = C * dist (e (u n)) y := by rw [e.apply_symm_apply]
    _ < C * (ε / C) := mul_lt_mul_of_pos_left hn' hC
    _ = ε := by rw [mul_comm, div_mul_cancel₀ _ hC.ne']

/-- A form distance for the relative perturbation is complete on the same domain.
The distance identities specify the original and perturbed shifted forms on differences. -/
theorem complete_of_relative_bound {D E F : Type*}
    [PseudoMetricSpace E] [CompleteSpace E] [PseudoMetricSpace F]
    (e : F ≃ E) (difference : F → F → D)
    (q v N : D → ℝ) (m a b : ℝ)
    (hm : 0 ≤ m) (ha₀ : 0 ≤ a) (ha : a < 1) (hb : 0 ≤ b)
    (hN : ∀ x, 0 ≤ N x) (hq : ∀ x, -m * N x ≤ q x)
    (hv : ∀ x, |v x| ≤ a * q x + b * N x)
    (original : ∀ x y, dist (e x) (e y) ^ 2 =
      q (difference x y) + (m + 1) * N (difference x y))
    (perturbed : ∀ x y, dist x y ^ 2 =
      q (difference x y) + v (difference x y) +
        ((1 - a) * (m + 1) + b) * N (difference x y)) :
    CompleteSpace F := by
  have hc : 0 < 1 - a := sub_pos.mpr ha
  have hC : 0 < 1 + a + 2 * b := by nlinarith
  apply complete_of_distance_comparison e (Real.sqrt (1 - a)) (Real.sqrt (1 + a + 2 * b))
    (Real.sqrt_pos.mpr hc) (Real.sqrt_pos.mpr hC)
  · intro x y
    apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) dist_nonneg) dist_nonneg).mp
    rw [mul_pow, Real.sq_sqrt hc.le, original x y, perturbed x y]
    exact (Paper10RelativeFormBounds.shifted_comparison q v N m a b hm ha₀ hb hN hq hv _).1
  · intro x y
    apply (sq_le_sq₀ dist_nonneg (mul_nonneg (Real.sqrt_nonneg _) dist_nonneg)).mp
    rw [mul_pow, Real.sq_sqrt hC.le, original x y, perturbed x y]
    exact (Paper10RelativeFormBounds.shifted_comparison q v N m a b hm ha₀ hb hN hq hv _).2

end ManuscriptAudit.Paper10RelativeFormClosed

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper10RelativeFormClosed.complete_of_relative_bound
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
