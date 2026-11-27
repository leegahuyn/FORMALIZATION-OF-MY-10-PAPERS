import Lean.Util.CollectAxioms
import Mathlib.Analysis.Normed.Group.Tannery
import PrimalitySheafVerification.ManuscriptAudit.Paper8ReciprocalCommonFourier
import PrimalitySheafVerification.ManuscriptAudit.Paper8SeparatePrintedLowerContours

/-!
# The remaining signed-modulus convergence condition

For each frequency one needs convergence of the modulus partial
sums, with a bound uniform in the modulus cutoff and summable after
multiplication by the inverse-nome powers. Polynomial growth in the
frequency suffices. This file proves the conditional analytic step
without an arithmetic cancellation axiom.

For relatively prime residues the classical source is Rhoades,
Theorem 1.1 and §3, https://arxiv.org/pdf/1111.1495 , which uses
Bringmann–Ono, Theorem 4.1 and Corollary 4.2(2),
https://uva.theopenscholar.com/files/ken-ono/files/098_8.pdf .
The cancellation estimates themselves are not formalized here.
-/

namespace ManuscriptAudit.Paper8ReciprocalCommonCancellation

open Filter
open scoped Topology
open Paper8ReciprocalCommonFourier (orderedFourierCoefficient finite_modulus_sum_hasSum)
open Paper8SeparateContourSeries (orderedPartialSum)
open Paper8SeparateReciprocalContourSeries (commonTerm)
open Paper8SeparatePrintedLowerContours (printed_ordered_convergence_iff_common)
open Paper8LiteralContourLimits (printedOuterPartialSum)
open Paper8HolomorphicPartPhase (qParameter)

noncomputable section

theorem common_ordered_limit_of_mode_limits (S : ∀ k : ℕ, Finset (Fin (2 * k))) {Q : ℂ}
    (hQ : ‖Q‖ < 1) (a : ℕ → ℂ) (M : ℕ → ℝ)
    (hCoefficients : ∀ n : ℕ, Tendsto (fun N => orderedFourierCoefficient S N n) atTop (𝓝 (a n)))
    (hBound : ∀ᶠ N in atTop, ∀ n : ℕ, ‖orderedFourierCoefficient S N n‖ ≤ M n)
    (hSummable : Summable (fun n : ℕ => M n * ‖Q‖ ^ n)) :
    Tendsto (orderedPartialSum (fun k => commonTerm S (k + 1) Q)) atTop
      (𝓝 (∑' n : ℕ, a n * Q ^ n)) := by
  let B (N n : ℕ) := orderedFourierCoefficient S N n * Q ^ n
  have hP (n : ℕ) : Tendsto (fun N => B N n) atTop (𝓝 (a n * Q ^ n)) :=
    (hCoefficients n).mul tendsto_const_nhds
  have hD : ∀ᶠ N in atTop, ∀ n : ℕ, ‖B N n‖ ≤ M n * ‖Q‖ ^ n := by
    filter_upwards [hBound] with N hN
    intro n
    unfold B
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right (hN n) (pow_nonneg (norm_nonneg _) _)
  have hT : Tendsto (fun N => ∑' n : ℕ, B N n) atTop (𝓝 (∑' n : ℕ, a n * Q ^ n)) :=
    tendsto_tsum_of_dominated_convergence hSummable hP hD
  exact hT.congr fun N => (finite_modulus_sum_hasSum S N hQ).tsum_eq

theorem common_ordered_limit_of_polynomial_mode_bound (S : ∀ k : ℕ, Finset (Fin (2 * k))) {Q : ℂ}
    (hQ : ‖Q‖ < 1) (a : ℕ → ℂ) (C : ℝ) (b : ℕ)
    (hCoefficients : ∀ n : ℕ, Tendsto (fun N => orderedFourierCoefficient S N n) atTop (𝓝 (a n)))
    (hBound : ∀ᶠ N in atTop, ∀ n : ℕ,
      ‖orderedFourierCoefficient S N n‖ ≤ C * (1 + (n : ℝ) ^ b)) :
    Tendsto (orderedPartialSum (fun k => commonTerm S (k + 1) Q)) atTop
      (𝓝 (∑' n : ℕ, a n * Q ^ n)) := by
  have hReal : ‖(‖Q‖ : ℝ)‖ < 1 := by simpa only [Real.norm_of_nonneg (norm_nonneg Q)] using hQ
  have hG : Summable (fun n : ℕ => ‖Q‖ ^ n) := summable_geometric_of_norm_lt_one hReal
  have hP : Summable (fun n : ℕ => (n : ℝ) ^ b * ‖Q‖ ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one b hReal
  refine common_ordered_limit_of_mode_limits S hQ a (fun n => C * (1 + (n : ℝ) ^ b))
    hCoefficients hBound ?_
  exact ((hG.add hP).mul_left C).congr (fun n => by ring)

theorem printed_pair_converges_of_polynomial_mode_bound (S : ∀ k : ℕ, Finset (Fin (2 * k)))
    {z : ℂ} (hz : z.im < 0) (hq : ‖qParameter (-z)‖ ≤ 1 / 4)
    (a : ℕ → ℂ) (C : ℝ) (b : ℕ)
    (hCoefficients : ∀ n : ℕ, Tendsto (fun N => orderedFourierCoefficient S N n) atTop (𝓝 (a n)))
    (hBound : ∀ᶠ N in atTop, ∀ n : ℕ,
      ‖orderedFourierCoefficient S N n‖ ≤ C * (1 + (n : ℝ) ^ b)) :
    (∃ L : ℂ, Tendsto (printedOuterPartialSum 23 24 S z) atTop (𝓝 L)) ∧
      (∃ L : ℂ, Tendsto (printedOuterPartialSum (2 / 3) 16 S z) atTop (𝓝 L)) := by
  have hLt : ‖qParameter (-z)‖ < 1 := hq.trans_lt (by norm_num)
  have hCommon := common_ordered_limit_of_polynomial_mode_bound S hLt a C b hCoefficients hBound
  exact ⟨(printed_ordered_convergence_iff_common 23 (by norm_num) le_rfl
      (by norm_num) (by norm_num) S hz hq).2 ⟨_, hCommon⟩,
    (printed_ordered_convergence_iff_common (2 / 3) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) S hz hq).2 ⟨_, hCommon⟩⟩

end
end ManuscriptAudit.Paper8ReciprocalCommonCancellation

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ReciprocalCommonCancellation.common_ordered_limit_of_mode_limits,
      ``ManuscriptAudit.Paper8ReciprocalCommonCancellation.common_ordered_limit_of_polynomial_mode_bound,
      ``ManuscriptAudit.Paper8ReciprocalCommonCancellation.printed_pair_converges_of_polynomial_mode_bound] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
