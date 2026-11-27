import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import PrimalitySheafVerification.ManuscriptAudit.PadicHenselGate

/-! The affine residual fibre has a free coordinate at any nonsingular point. -/

namespace ManuscriptAudit.Paper2PadicWeierstrassLift

open Polynomial WeierstrassCurve PadicHenselGate

noncomputable section

variable {p : ℕ} [Fact p.Prime]

private abbrev red : ℤ_[p] →+* ZMod p := PadicInt.toZMod

private def yPolynomial (W : WeierstrassCurve ℤ_[p]) (x : ℤ_[p]) :
    Polynomial ℤ_[p] :=
  X ^ 2 + C (W.a₁ * x + W.a₃) * X - C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)

private def xPolynomial (W : WeierstrassCurve ℤ_[p]) (y : ℤ_[p]) :
    Polynomial ℤ_[p] :=
  C (y ^ 2 + W.a₃ * y) + C (W.a₁ * y) * X - (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)

private theorem eval_y (W : WeierstrassCurve ℤ_[p]) (x y : ℤ_[p]) :
    (yPolynomial W x).aeval y =
      y ^ 2 + W.a₁ * x * y + W.a₃ * y - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) := by
  simp only [yPolynomial, coe_aeval_eq_eval, eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  ring

private theorem eval_x (W : WeierstrassCurve ℤ_[p]) (x y : ℤ_[p]) :
    (xPolynomial W y).aeval x =
      y ^ 2 + W.a₁ * x * y + W.a₃ * y - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) := by
  simp only [xPolynomial, coe_aeval_eq_eval, eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  ring

private theorem derivative_y (W : WeierstrassCurve ℤ_[p]) (x y : ℤ_[p]) :
    (yPolynomial W x).derivative.aeval y = 2 * y + W.a₁ * x + W.a₃ := by
  simp only [yPolynomial, derivative_sub, derivative_add, derivative_C, derivative_C_mul,
    derivative_X, derivative_X_pow, coe_aeval_eq_eval, eval_add, eval_mul, eval_C, eval_X,
    eval_pow, mul_one, sub_zero]
  push_cast
  ring

private theorem derivative_x (W : WeierstrassCurve ℤ_[p]) (x y : ℤ_[p]) :
    (xPolynomial W y).derivative.aeval x = W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) := by
  simp only [xPolynomial, derivative_sub, derivative_add, derivative_C, derivative_C_mul,
    derivative_X, derivative_X_pow, coe_aeval_eq_eval, eval_sub, eval_add, eval_mul, eval_C,
    eval_X, eval_pow, mul_one, zero_add, add_zero]
  push_cast
  ring

/-- For every lift of the first coordinate, a simple second-coordinate residue has exactly one lift. -/
theorem lift_second (W : WeierstrassCurve ℤ_[p]) {u v : ZMod p}
    (hEq : (W.map red).toAffine.Equation u v)
    (hDerivative : 2 * v + (W.map red).a₁ * u + (W.map red).a₃ ≠ 0)
    (x : ℤ_[p]) (hx : red x = u) :
    ∃! y : ℤ_[p], W.toAffine.Equation x y ∧ red y = v := by
  obtain ⟨y, hy⟩ := (ZMod.ringHom_surjective (red : ℤ_[p] →+* ZMod p)) v
  have hRoot : red ((yPolynomial W x).aeval y) = 0 := by
    rw [eval_y]
    simpa only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, map_add, map_mul, map_pow, map_sub,
      hx, hy] using (Affine.equation_iff' (W := (W.map red).toAffine) u v).mp hEq
  have hSimple : red ((yPolynomial W x).derivative.aeval y) ≠ 0 := by
    rw [derivative_y]
    simpa only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃,
      map_add, map_mul, map_ofNat, hx, hy] using hDerivative
  simpa only [eval_y, ← Affine.equation_iff', hy] using
    unique_lift_from_simple (yPolynomial W x) y hRoot hSimple

/-- For every lift of the second coordinate, a simple first-coordinate residue has exactly one lift. -/
theorem lift_first (W : WeierstrassCurve ℤ_[p]) {u v : ZMod p}
    (hEq : (W.map red).toAffine.Equation u v)
    (hDerivative : (W.map red).a₁ * v -
      (3 * u ^ 2 + 2 * (W.map red).a₂ * u + (W.map red).a₄) ≠ 0)
    (y : ℤ_[p]) (hy : red y = v) :
    ∃! x : ℤ_[p], W.toAffine.Equation x y ∧ red x = u := by
  obtain ⟨x, hx⟩ := (ZMod.ringHom_surjective (red : ℤ_[p] →+* ZMod p)) u
  have hRoot : red ((xPolynomial W y).aeval x) = 0 := by
    rw [eval_x]
    simpa only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, map_add, map_mul, map_pow, map_sub,
      hx, hy] using (Affine.equation_iff' (W := (W.map red).toAffine) u v).mp hEq
  have hSimple : red ((xPolynomial W y).derivative.aeval x) ≠ 0 := by
    rw [derivative_x]
    simpa only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄,
      map_add, map_mul, map_sub, map_pow, map_ofNat, hx, hy] using hDerivative
  simpa only [eval_x, ← Affine.equation_iff', hx] using
    unique_lift_from_simple (xPolynomial W y) x hRoot hSimple

/-- The literal affine lifts with both prescribed residues. -/
abbrev Lifts (W : WeierstrassCurve ℤ_[p]) (u v : ZMod p) :=
  { xy : ℤ_[p] × ℤ_[p] // W.toAffine.Equation xy.1 xy.2 ∧ red xy.1 = u ∧ red xy.2 = v }

private def coordinateLifts (u : ZMod p) : ℕ ↪ {x : ℤ_[p] // red x = u} := by
  let h := (ZMod.ringHom_surjective (red : ℤ_[p] →+* ZMod p)) u
  let x := Classical.choose h
  have hx : red x = u := Classical.choose_spec h
  have h₀ : (p : ZMod p) = 0 := ZMod.natCast_self p
  have hp : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  refine ⟨fun n => ⟨x + (p : ℤ_[p]) * n, ?_⟩, ?_⟩
  · rw [map_add, map_mul, map_natCast, h₀, zero_mul, add_zero, hx]
  · intro a b hab
    have hmul : (p : ℤ_[p]) * a = (p : ℤ_[p]) * b :=
      add_left_cancel (congrArg Subtype.val hab)
    exact_mod_cast mul_left_cancel₀ hp hmul

/-- Each nonsingular affine residue point has infinitely many simultaneous p-adic lifts. -/
theorem infinitely_many_lifts (W : WeierstrassCurve ℤ_[p]) {u v : ZMod p}
    (h : (W.map red).toAffine.Nonsingular u v) : Infinite (Lifts W u v) := by
  obtain ⟨hEq, hX | hY⟩ := (Affine.nonsingular_iff' (W := (W.map red).toAffine) u v).mp h
  · let fy := coordinateLifts v
    let hLift (n : ℕ) := ExistsUnique.exists (lift_first W hEq hX (fy n).1 (fy n).2)
    let f (n : ℕ) : Lifts W u v :=
      ⟨(Classical.choose (hLift n), (fy n).1), (Classical.choose_spec (hLift n)).1,
        (Classical.choose_spec (hLift n)).2, (fy n).2⟩
    exact Infinite.of_injective f (fun a b hab => fy.injective
      (Subtype.ext (congrArg (fun z : Lifts W u v => z.1.2) hab)))
  · let fx := coordinateLifts u
    let hLift (n : ℕ) := ExistsUnique.exists (lift_second W hEq hY (fx n).1 (fx n).2)
    let f (n : ℕ) : Lifts W u v :=
      ⟨((fx n).1, Classical.choose (hLift n)), (Classical.choose_spec (hLift n)).1,
        (fx n).2, (Classical.choose_spec (hLift n)).2⟩
    exact Infinite.of_injective f (fun a b hab => fx.injective
      (Subtype.ext (congrArg (fun z : Lifts W u v => z.1.1) hab)))

end
end ManuscriptAudit.Paper2PadicWeierstrassLift

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper2PadicWeierstrassLift.lift_first,
      ``ManuscriptAudit.Paper2PadicWeierstrassLift.lift_second,
      ``ManuscriptAudit.Paper2PadicWeierstrassLift.infinitely_many_lifts] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
