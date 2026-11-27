import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Topology.Sequences

/-! An approximate eigenvector sequence with uniformly separated terms excludes a compact inverse. -/

namespace ManuscriptAudit.CompactInverseSeparatedApproximateEigenvectors

open Filter Set
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

theorem no_compact_left_inverse (T : H →ₗ.[ℂ] H) (u : ℕ → T.domain) (λ μ : ℂ)
    (hNorm : ∀ n, ‖(u n : H)‖ = 1)
    (hSep : ∀ m n : ℕ, m < n → 1 ≤ dist (u m : H) (u n : H))
    (hA : Tendsto (fun n => T (u n) - λ • (u n : H)) atTop (𝓝 0)) :
    ¬ ∃ B : H →L[ℂ] H, IsCompactOperator (B : H →ₗ[ℂ] H) ∧
      ∀ v : T.domain, B (T v - μ • (v : H)) = v := by
  rintro ⟨B, hC, hInv⟩
  let K := closure ((B : H → H) '' Metric.closedBall 0 1)
  have hc : IsCompact K := hC.isCompact_closure_image_closedBall 1
  have hIn (n : ℕ) : B (u n : H) ∈ K := by
    apply subset_closure
    exact ⟨(u n : H), by simp [Metric.mem_closedBall, dist_zero_right, hNorm n], rfl⟩
  obtain ⟨b, _, f, hf, hB⟩ := hc.tendsto_subseq hIn
  let e (n : ℕ) := T (u n) - λ • (u n : H)
  have hDecomp (n : ℕ) : B (e n) + (λ - μ) • B (u n : H) = (u n : H) := by
    rw [← map_smul, ← map_add]
    have hEq : e n + (λ - μ) • (u n : H) = T (u n) - μ • (u n : H) := by
      dsimp only [e]
      rw [sub_smul]
      abel
    rw [hEq, hInv]
  have hz : Tendsto (fun n => B (e (f n))) atTop (𝓝 0) := by
    have he := hA.comp hf.tendsto_atTop
    simpa only [map_zero, Function.comp_apply] using (B.continuous.tendsto 0).comp he
  have hv : Tendsto (fun n => (u (f n) : H)) atTop (𝓝 ((λ - μ) • b)) := by
    have h := hz.add (hB.const_smul (λ - μ))
    simpa only [Function.comp_apply, hDecomp, zero_add] using h
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hv) (1 / 4) (by norm_num)
  have h₁ := hN N le_rfl
  have h₂ := hN (N + 1) (Nat.le_succ N)
  have hl := hSep (f N) (f (N + 1)) (hf (Nat.lt_succ_self N))
  have ht := dist_triangle_right (u (f N) : H) (u (f (N + 1)) : H) ((λ - μ) • b)
  linarith

end ManuscriptAudit.CompactInverseSeparatedApproximateEigenvectors

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CompactInverseSeparatedApproximateEigenvectors.no_compact_left_inverse
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
