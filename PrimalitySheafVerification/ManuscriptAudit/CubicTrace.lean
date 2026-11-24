import Lean.Elab.Tactic.Omega
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Mathlib.Data.Fintype.Option
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Ring

namespace PrimalitySheafVerification.ManuscriptAudit

noncomputable section

/-!
Paper 5, physical PDF pp. 158–162. Listing 1 uses the reduction prime as
the coefficient `p` in the model `y² = x³ - p*x + A`. The results here count
points for that family of reductions. If the integer coefficient `pₙ` is
fixed while the reduction prime varies, this argument applies to the
reduction at `p = pₙ`.

For the finite geometric exception claim, a separate theorem must show that
trace zero implies geometric supersingularity for these actual smooth
reductions, for example by proving that their geometric `p`-torsion consists
only of the identity. A refutation for the varying-prime family also needs
infinitely many primes congruent to 2 modulo 3 with nonzero reduction of
the chosen integer `A`. The trace-zero result by itself directly tests
the arithmetic label used in the paper and in its table.
-/

/-- The short Weierstrass equation from Paper 5, reduced in `ZMod p`. -/
def paper5TraceCurve (p : ℕ) (A : ZMod p) : WeierstrassCurve (ZMod p) where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := -(p : ZMod p)
  a₆ := A

/-- The literal affine solutions counted in the trace calculation. -/
abbrev Paper5TraceAffine (p : ℕ) (A : ZMod p) :=
  {xy : ZMod p × ZMod p // xy.2 ^ 2 = xy.1 ^ 3 - (p : ZMod p) * xy.1 + A}

private def paper5CubeEquiv {p : ℕ} [Fact p.Prime]
    (hp : 5 ≤ p) (hr : p % 3 = 2) : ZMod p ≃ ZMod p := by
  let d := (2 * p - 1) / 3
  have he : 3 * d = (p - 1) * 2 + 1 := by
    dsimp [d]
    omega
  have hpow (x : ZMod p) : x ^ (3 * d) = x := by
    by_cases hx : x = 0
    · rw [hx, zero_pow (by omega : 3 * d ≠ 0)]
    · rw [he, pow_add, pow_one, pow_mul, ZMod.pow_card_sub_one_eq_one hx, one_pow, one_mul]
  refine
    { toFun := fun x => x ^ 3
      invFun := fun x => x ^ d
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    change (x ^ 3) ^ d = x
    rw [← pow_mul]
    exact hpow x
  · intro x
    change (x ^ d) ^ 3 = x
    rw [← pow_mul, Nat.mul_comm d 3]
    exact hpow x

private def paper5AffineEquiv {p : ℕ} [Fact p.Prime]
    (hp : 5 ≤ p) (hr : p % 3 = 2) (A : ZMod p) : Paper5TraceAffine p A ≃ ZMod p := by
  let e := paper5CubeEquiv hp hr
  refine
    { toFun := fun xy => xy.1.2
      invFun := fun y => ⟨(e.symm (y ^ 2 - A), y), ?_⟩
      left_inv := ?_
      right_inv := fun _ => rfl }
  · change y ^ 2 = (e.symm (y ^ 2 - A)) ^ 3 - (p : ZMod p) * e.symm (y ^ 2 - A) + A
    rw [ZMod.natCast_self, zero_mul, sub_zero]
    have h : (e.symm (y ^ 2 - A)) ^ 3 = y ^ 2 - A := e.apply_symm_apply _
    rw [h, sub_add_cancel]
  · rintro ⟨⟨x, y⟩, h⟩
    apply Subtype.ext
    change (e.symm (y ^ 2 - A), y) = (x, y)
    refine Prod.ext ?_ rfl
    apply e.injective
    rw [e.apply_symm_apply]
    change y ^ 2 - A = x ^ 3
    exact (sub_eq_iff_eq_add).2 (by simpa [ZMod.natCast_self] using h)

private theorem paper5_smallCast_ne_zero {p n : ℕ}
    (hn : 0 < n) (hlt : n < p) : (n : ZMod p) ≠ 0 := by
  intro he
  have hv : n = 0 := by
    simpa only [ZMod.val_natCast, ZMod.val_zero, Nat.mod_eq_of_lt hlt] using congrArg ZMod.val he
  omega

/-- The reduced curve is smooth for a nonzero constant in the indicated characteristics. -/
theorem paper5_traceCurve_discriminant_ne_zero {p : ℕ} [Fact p.Prime]
    (hp : 5 ≤ p) {A : ZMod p} (hA : A ≠ 0) : (paper5TraceCurve p A).Δ ≠ 0 := by
  have hthree : (3 : ZMod p) ≠ 0 := paper5_smallCast_ne_zero (n := 3) (by omega) (by omega)
  have hfour : (4 : ZMod p) ≠ 0 := paper5_smallCast_ne_zero (n := 4) (by omega) (by omega)
  have hΔ : (paper5TraceCurve p A).Δ = -((3 : ZMod p) ^ 3 * (4 * A) ^ 2) := by
    simp [paper5TraceCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈] <;> ring <;> simp
  rw [hΔ]
  exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 3 hthree) (pow_ne_zero 2 (mul_ne_zero hfour hA)))

private theorem paper5_nonsingular_iff {p : ℕ} [Fact p.Prime]
    (hp : 5 ≤ p) {A : ZMod p} (hA : A ≠ 0) (x y : ZMod p) :
    (paper5TraceCurve p A).toProjective.toAffine.Nonsingular x y ↔
      y ^ 2 = x ^ 3 - (p : ZMod p) * x + A := by
  rw [← WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero
    (paper5_traceCurve_discriminant_ne_zero hp hA)]
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [paper5TraceCurve]

private noncomputable def paper5ProjectiveEquiv {p : ℕ} [Fact p.Prime]
    (hp : 5 ≤ p) (hr : p % 3 = 2) {A : ZMod p} (hA : A ≠ 0) :
    (paper5TraceCurve p A).toProjective.Point ≃ Option (ZMod p) := by
  classical
  let W := (paper5TraceCurve p A).toProjective
  let e₁ : W.Point ≃ W.toAffine.Point :=
    (WeierstrassCurve.Projective.Point.toAffineAddEquiv (W := W)).toEquiv
  let e₂ : W.toAffine.Point ≃ Option {xy : ZMod p × ZMod p // W.toAffine.Nonsingular xy.1 xy.2} :=
    W.toAffine.nonsingularPointEquiv
  let e₃ : {xy : ZMod p × ZMod p // W.toAffine.Nonsingular xy.1 xy.2} ≃ Paper5TraceAffine p A :=
    { toFun := fun xy => ⟨xy.1, (paper5_nonsingular_iff hp hA _ _).1 xy.2⟩
      invFun := fun xy => ⟨xy.1, (paper5_nonsingular_iff hp hA _ _).2 xy.2⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }
  exact e₁.trans (e₂.trans (e₃.trans (paper5AffineEquiv hp hr A)).optionCongr)

/-- There is one affine solution for each choice of the second coordinate. -/
theorem paper5_traceCurve_affine_count {p : ℕ} [Fact p.Prime]
    (hp : 5 ≤ p) (hr : p % 3 = 2) (A : ZMod p) : Nat.card (Paper5TraceAffine p A) = p := by
  calc
    Nat.card (Paper5TraceAffine p A) = Nat.card (ZMod p) := Nat.card_congr (paper5AffineEquiv hp hr A)
    _ = p := by rw [Nat.card_eq_fintype_card, ZMod.card]

/-- The actual projective Weierstrass curve has one additional point at infinity. -/
theorem paper5_traceCurve_projective_count {p : ℕ} [Fact p.Prime]
    (hp : 5 ≤ p) (hr : p % 3 = 2) {A : ZMod p} (hA : A ≠ 0) :
    Nat.card (paper5TraceCurve p A).toProjective.Point = p + 1 := by
  calc
    Nat.card (paper5TraceCurve p A).toProjective.Point = Nat.card (Option (ZMod p)) :=
      Nat.card_congr (paper5ProjectiveEquiv hp hr hA)
    _ = p + 1 := by rw [Nat.card_eq_fintype_card, Fintype.card_option, ZMod.card]

/-- The integer point-count trace for the reduced curve is zero. -/
theorem paper5_traceCurve_trace_eq_zero {p : ℕ} [Fact p.Prime]
    (hp : 5 ≤ p) (hr : p % 3 = 2) {A : ZMod p} (hA : A ≠ 0) :
    (p : ℤ) + 1 - (Nat.card (paper5TraceCurve p A).toProjective.Point : ℤ) = 0 := by
  rw [paper5_traceCurve_projective_count hp hr hA]
  simp

end

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``paper5_traceCurve_discriminant_ne_zero, ``paper5_traceCurve_affine_count,
      ``paper5_traceCurve_projective_count, ``paper5_traceCurve_trace_eq_zero] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"

end PrimalitySheafVerification.ManuscriptAudit
