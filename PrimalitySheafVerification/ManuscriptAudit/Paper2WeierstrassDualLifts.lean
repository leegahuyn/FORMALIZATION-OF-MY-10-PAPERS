import Lean.Util.CollectAxioms
import Mathlib.Algebra.DualNumber
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.Tactic.LinearCombination

/-! Actual square-zero deformations of nonsingular affine Weierstrass points. -/

namespace ManuscriptAudit.Paper2WeierstrassDualLifts

open WeierstrassCurve
open scoped DualNumber

section Ring

variable {K : Type*} [CommRing K]

def value (W : WeierstrassCurve K) (x y : K) : K :=
  y ^ 2 + W.a₁ * x * y + W.a₃ * y - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)

def dx (W : WeierstrassCurve K) (x y : K) : K :=
  W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)

def dy (W : WeierstrassCurve K) (x y : K) : K :=
  2 * y + W.a₁ * x + W.a₃

private theorem dual_value (W : WeierstrassCurve K) (x y a b : K) :
    value (W.map (algebraMap K K[ε])) ⟨x, a⟩ ⟨y, b⟩ =
    (⟨value W x y, dx W x y * a + dy W x y * b⟩ : K[ε]) := by
  have hy_sq : ((⟨y, b⟩ : K[ε]) ^ 2) =
      (⟨y * y, y * b + b * y⟩ : K[ε]) := by
    rw [pow_two] <;> rfl
  have hx_sq : ((⟨x, a⟩ : K[ε]) ^ 2) =
      (⟨x * x, x * a + a * x⟩ : K[ε]) := by
    rw [pow_two] <;> rfl
  have hx_cube : ((⟨x, a⟩ : K[ε]) ^ 3) =
      (⟨(x * x) * x, (x * x) * a + (x * a + a * x) * x⟩ : K[ε]) := by
    rw [show (3 : ℕ) = 2 + 1 by decide, pow_succ, hx_sq] <;> rfl
  unfold value
  rw [hy_sq, hx_sq, hx_cube]
  apply TrivSqZeroExt.ext
  · change y * y + W.a₁ * x * y + W.a₃ * y -
        ((x * x) * x + W.a₂ * (x * x) + W.a₄ * x + W.a₆) =
      y ^ 2 + W.a₁ * x * y + W.a₃ * y - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)
    ring
  · change y * b + b * y + (W.a₁ * x * b + (W.a₁ * a + 0 * x) * y) +
        (W.a₃ * b + 0 * y) -
        ((x * x * a + (x * a + a * x) * x) +
          (W.a₂ * (x * a + a * x) + 0 * (x * x)) + (W.a₄ * a + 0 * x) + 0) =
      dx W x y * a + dy W x y * b
    unfold dx dy
    ring

/-- The actual Weierstrass equation over the dual numbers is its exact first variation. -/
theorem equation_iff (W : WeierstrassCurve K) (x y a b : K) :
    (W.map (algebraMap K K[ε])).toAffine.Equation ⟨x, a⟩ ⟨y, b⟩ ↔
      W.toAffine.Equation x y ∧ dx W x y * a + dy W x y * b = 0 := by
  rw [Affine.equation_iff' (W := (W.map (algebraMap K K[ε])).toAffine) ⟨x, a⟩ ⟨y, b⟩,
    Affine.equation_iff' (W := W.toAffine) x y]
  change value (W.map (algebraMap K K[ε])) ⟨x, a⟩ ⟨y, b⟩ = 0 ↔
    value W x y = 0 ∧ dx W x y * a + dy W x y * b = 0
  rw [dual_value]
  constructor
  · intro h
    exact ⟨congrArg TrivSqZeroExt.fst h, congrArg TrivSqZeroExt.snd h⟩
  · rintro ⟨h₀, h₁⟩
    exact TrivSqZeroExt.ext h₀ h₁

abbrev DualLifts (W : WeierstrassCurve K) (x y : K) :=
  { ab : K × K //
    (W.map (algebraMap K K[ε])).toAffine.Equation ⟨x, ab.1⟩ ⟨y, ab.2⟩ }

end Ring

section Field

variable {K : Type*} [Field K]

private def firstCoordinate (W : WeierstrassCurve K) (x y : K)
    (hEq : W.toAffine.Equation x y) (hY : dy W x y ≠ 0) :
    DualLifts W x y ≃ K where
  toFun z := z.1.1
  invFun a := ⟨⟨a, -(dx W x y * a) / dy W x y⟩, (equation_iff W x y _ _).mpr
    ⟨hEq, by field_simp [hY] <;> ring⟩⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change -(dx W x y * z.1.1) / dy W x y = z.1.2
      apply (div_eq_iff hY).2
      have h := ((equation_iff W x y _ _).mp z.2).2
      linear_combination -h
  right_inv _ := rfl

private def secondCoordinate (W : WeierstrassCurve K) (x y : K)
    (hEq : W.toAffine.Equation x y) (hX : dx W x y ≠ 0) :
    DualLifts W x y ≃ K where
  toFun z := z.1.2
  invFun b := ⟨⟨-(dy W x y * b) / dx W x y, b⟩, (equation_iff W x y _ _).mpr
    ⟨hEq, by field_simp [hX] <;> ring⟩⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · change -(dy W x y * z.1.2) / dx W x y = z.1.1
      apply (div_eq_iff hX).2
      have h := ((equation_iff W x y _ _).mp z.2).2
      linear_combination -h
    · rfl
  right_inv _ := rfl

/-- Every nonsingular affine point has a one-parameter family of actual first-order lifts. -/
theorem dual_lifts_of_nonsingular (W : WeierstrassCurve K) (x y : K)
    (h : W.toAffine.Nonsingular x y) : Nonempty (DualLifts W x y ≃ K) := by
  obtain ⟨hEq, hX | hY⟩ := (Affine.nonsingular_iff' (W := W.toAffine) x y).mp h
  · exact ⟨secondCoordinate W x y hEq hX⟩
  · exact ⟨firstCoordinate W x y hEq hY⟩

theorem nonunique_dual_lift (W : WeierstrassCurve K) (x y : K)
    (h : W.toAffine.Nonsingular x y) : ¬ Subsingleton (DualLifts W x y) := by
  obtain ⟨e⟩ := dual_lifts_of_nonsingular W x y h
  intro hUnique
  exact zero_ne_one (e.symm.injective (hUnique.elim (e.symm 0) (e.symm 1)))

end Field

end ManuscriptAudit.Paper2WeierstrassDualLifts

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper2WeierstrassDualLifts.equation_iff,
      ``ManuscriptAudit.Paper2WeierstrassDualLifts.dual_lifts_of_nonsingular,
      ``ManuscriptAudit.Paper2WeierstrassDualLifts.nonunique_dual_lift] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
