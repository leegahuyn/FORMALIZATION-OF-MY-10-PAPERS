import Lean.Util.CollectAxioms
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! A uniformly separated family inside a compact set has finitely many labels. -/

namespace ManuscriptAudit.CompactSeparatedFamily

variable {I E : Type*} [PseudoMetricSpace E]

/-- A finite half-radius cover gives an injection from the labels into a finite set. -/
theorem finite_index (f : I → E) (K : Set E) (hK : IsCompact K)
    (hmem : ∀ i, f i ∈ K) (r : ℝ) (hr : 0 < r)
    (hsep : ∀ i j, i ≠ j → r ≤ dist (f i) (f j)) : Finite I := by
  classical
  obtain ⟨t, _, ht, hcover⟩ := finite_cover_balls_of_compact hK
    (show 0 < r / 2 by positivity)
  have hex (i : I) : ∃ y : t, dist (f i) y < r / 2 := by
    have hi := hcover (hmem i)
    simp only [Set.mem_iUnion, Metric.mem_ball] at hi
    obtain ⟨x, hx, hdist⟩ := hi
    exact ⟨⟨x, hx⟩, hdist⟩
  choose c hc using hex
  letI := ht.fintype
  apply Finite.of_injective c
  intro i j h
  by_contra hij
  have hd₁ : dist (f i) (c i) < r / 2 := hc i
  have hd₂ : dist (f j) (c i) < r / 2 := by rw [h]; exact hc j
  have hd := (dist_triangle_right (f i) (f j) (c i))
  have hs := hsep i j hij
  linarith

end ManuscriptAudit.CompactSeparatedFamily

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CompactSeparatedFamily.finite_index
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
