import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper7CommonEulerPointwise

/-! A common elliptic Euler argument gives no continuous pointwise realization near zero. -/

namespace ManuscriptAudit.Paper7CommonEulerContinuity

open Filter Topology Paper7CommonEulerPointwise

theorem no_continuous_pointwise_limit {q : ℕ → ℕ} {a : ℕ → ℂ}
    (hq : Tendsto (fun n => (q n : ℝ)) atTop atTop)
    (hHasse : ∀ n, ‖a n‖ ≤ 2 * Real.sqrt (q n : ℝ)) {r : ℝ} (hr : 0 < r) :
    ¬ ∃ g : ℂ → ℂ, ContinuousAt g 0 ∧
      ∀ z : ℂ, ‖z‖ < r → Tendsto (partialProduct q a z) atTop (𝓝 (g z)) := by
  rintro ⟨g, hg, hPoint⟩
  have hOrigin : Tendsto (partialProduct q a 0) atTop (𝓝 (1 : ℂ)) := by
    have hSeq : partialProduct q a 0 = fun _ => (1 : ℂ) :=
      funext (partialProduct_zero_argument q a)
    rw [hSeq]
    exact tendsto_const_nhds
  have g0 : g 0 = 1 := tendsto_nhds_unique (hPoint 0 (by simpa using hr)) hOrigin
  obtain ⟨δ, hδ, hClose⟩ := Metric.continuousAt_iff.mp hg (1 / 2) (by norm_num)
  let t : ℝ := min r δ / 2
  let z : ℂ := t
  have ht : 0 < t := div_pos (lt_min hr hδ) two_pos
  have hz : z ≠ 0 := by
    dsimp only [z]
    exact_mod_cast ht.ne'
  have hNorm : ‖z‖ = t := by
    simp only [z, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  have htr : t < r := (half_lt_self (lt_min hr hδ)).trans_le (min_le_left r δ)
  have htδ : t < δ := (half_lt_self (lt_min hr hδ)).trans_le (min_le_right r δ)
  have gz : g z = 0 :=
    tendsto_nhds_unique (hPoint z (hNorm.trans_lt htr)) (tendsto_at_nonzero hq hHasse hz)
  have hOut := hClose (x := z) (by rwa [dist_zero_right, hNorm])
  rw [gz, g0, dist_zero_left, norm_one] at hOut
  norm_num at hOut

end ManuscriptAudit.Paper7CommonEulerContinuity

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.Paper7CommonEulerContinuity.no_continuous_pointwise_limit
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
