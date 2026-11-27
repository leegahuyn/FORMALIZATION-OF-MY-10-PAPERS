import Lean.Util.CollectAxioms
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.MetricSpace.Isometry
import PrimalitySheafVerification.ManuscriptAudit.Paper2PadicWeierstrassLift

/-! A nonsingular residual fibre is isometric to a residue ball by a free coordinate. -/

namespace ManuscriptAudit.Paper2PadicWeierstrassIsometry

open WeierstrassCurve PadicHenselGate Paper2PadicWeierstrassLift

noncomputable section

variable {p : ℕ} [Fact p.Prime]

private abbrev red : ℤ_[p] →+* ZMod p := PadicInt.toZMod

abbrev ResidueBall (u : ZMod p) := {x : ℤ_[p] // red x = u}

private theorem norm_eq_one_of_nonzero_residue (a : ℤ_[p]) (ha : red a ≠ 0) : ‖a‖ = 1 :=
  le_antisymm (PadicInt.norm_le_one _) (le_of_not_gt fun h =>
    ha ((norm_lt_one_iff_reduction_zero a).mp h))

theorem norm_comparison (W : WeierstrassCurve ℤ_[p]) {u v : ZMod p}
    (a b : Lifts W u v) :
    (2 * v + (W.map red).a₁ * u + (W.map red).a₃ ≠ 0 →
      ‖a.1.2 - b.1.2‖ ≤ ‖a.1.1 - b.1.1‖) ∧
    ((W.map red).a₁ * v - (3 * u ^ 2 + 2 * (W.map red).a₂ * u + (W.map red).a₄) ≠ 0 →
      ‖a.1.1 - b.1.1‖ ≤ ‖a.1.2 - b.1.2‖) := by
  let x := a.1.1
  let y := a.1.2
  let x' := b.1.1
  let y' := b.1.2
  let jY := y + y' + W.a₁ * x + W.a₃
  let jX := x ^ 2 + x * x' + x' ^ 2 + W.a₂ * (x + x') + W.a₄ - W.a₁ * y'
  have hx : red x = u := a.2.2.1
  have hy : red y = v := a.2.2.2
  have hx' : red x' = u := b.2.2.1
  have hy' : red y' = v := b.2.2.2
  have hEqA := (Affine.equation_iff' (W := W.toAffine) x y).mp a.2.1
  have hEqB := (Affine.equation_iff' (W := W.toAffine) x' y').mp b.2.1
  have hDifference : (y - y') * jY = (x - x') * jX := by
    dsimp only [jY, jX]
    linear_combination hEqA - hEqB
  have hNorm : ‖y - y'‖ * ‖jY‖ = ‖x - x'‖ * ‖jX‖ := by
    simpa only [norm_mul] using congrArg (fun z : ℤ_[p] => ‖z‖) hDifference
  constructor
  · intro hY
    have hRedY : red jY = 2 * v + (W.map red).a₁ * u + (W.map red).a₃ := by
      simp only [jY, map_add, map_mul, hx, hy, hy', WeierstrassCurve.map_a₁,
        WeierstrassCurve.map_a₃]
      ring
    have hNY := norm_eq_one_of_nonzero_residue jY (fun h => hY (hRedY.symm.trans h))
    rw [hNY, mul_one] at hNorm
    change ‖y - y'‖ ≤ ‖x - x'‖
    rw [hNorm]
    exact mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one _)
  · intro hX
    have hRedX : red jX =
        -((W.map red).a₁ * v - (3 * u ^ 2 + 2 * (W.map red).a₂ * u + (W.map red).a₄)) := by
      simp only [jX, map_add, map_mul, map_sub, map_pow, hx, hx', hy',
        WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄]
      ring
    have hNX := norm_eq_one_of_nonzero_residue jX (fun h => (neg_ne_zero.mpr hX) (hRedX.symm.trans h))
    rw [hNX, mul_one] at hNorm
    change ‖x - x'‖ ≤ ‖y - y'‖
    rw [← hNorm]
    exact mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one _)

theorem free_coordinate (W : WeierstrassCurve ℤ_[p]) {u v : ZMod p}
    (h : (W.map red).toAffine.Nonsingular u v) :
    Nonempty (Lifts W u v ≃ᵢ ResidueBall u) ∨ Nonempty (Lifts W u v ≃ᵢ ResidueBall v) := by
  obtain ⟨hEq, hX | hY⟩ := (Affine.nonsingular_iff' (W := (W.map red).toAffine) u v).mp h
  · let f (a : Lifts W u v) : ResidueBall v := ⟨a.1.2, a.2.2.2⟩
    have hIso : Isometry f := by
      apply Isometry.of_dist_eq
      intro a b
      change dist a.1.2 b.1.2 = max (dist a.1.1 b.1.1) (dist a.1.2 b.1.2)
      simp only [dist_eq_norm]
      exact (max_eq_right ((norm_comparison W a b).2 hX)).symm
    have hSurj : Function.Surjective f := by
      intro y
      obtain ⟨x, hx⟩ := (lift_first W hEq hX y.1 y.2).exists
      exact ⟨⟨(x, y.1), hx.1, hx.2, y.2⟩, Subtype.ext rfl⟩
    exact Or.inr ⟨⟨Equiv.ofBijective f ⟨hIso.injective, hSurj⟩, hIso⟩⟩
  · let f (a : Lifts W u v) : ResidueBall u := ⟨a.1.1, a.2.2.1⟩
    have hIso : Isometry f := by
      apply Isometry.of_dist_eq
      intro a b
      change dist a.1.1 b.1.1 = max (dist a.1.1 b.1.1) (dist a.1.2 b.1.2)
      simp only [dist_eq_norm]
      exact (max_eq_left ((norm_comparison W a b).1 hY)).symm
    have hSurj : Function.Surjective f := by
      intro x
      obtain ⟨y, hy⟩ := (lift_second W hEq hY x.1 x.2).exists
      exact ⟨⟨(x.1, y), hy.1, x.2, hy.2⟩, Subtype.ext rfl⟩
    exact Or.inl ⟨⟨Equiv.ofBijective f ⟨hIso.injective, hSurj⟩, hIso⟩⟩

end
end ManuscriptAudit.Paper2PadicWeierstrassIsometry

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper2PadicWeierstrassIsometry.norm_comparison,
      ``ManuscriptAudit.Paper2PadicWeierstrassIsometry.free_coordinate] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
