import Lean.Util.CollectAxioms
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinarySevenOneTwist
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinarySevenTwistParameters

/-! The six exact Frobenius conjugacy classes for the centered curves over F₇. -/

namespace ManuscriptAudit.Paper5OrdinarySevenTwistGeometry

open WeierstrassCurve CubicThreeTorsionOrdinate CubicFrobeniusScaling CubicPointScaling
open Paper5OrdinarySeven Paper5OrdinarySevenGeometry Paper5OrdinarySevenFrobenius
open Paper5OrdinarySevenOneTwist Paper5OrdinarySevenTwistParameters

noncomputable section

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

variable (L : Type*) [Field L] [Algebra (ZMod 7) L] [CharP L 7] [IsAlgClosed L] [DecidableEq L]

private abbrev W := (ordinaryCurve L).toAffine
private abbrev a (x : ZMod 7) := algebraMap (ZMod 7) L x
private abbrev g := FiniteField.frobeniusAlgHom (ZMod 7) L

/-- The sign and rotation taken from the finite coefficient table. -/
def signedRotation (r : Row) : AddMonoid.End (Points L) :=
  if r.negate then -(rotation L ^ r.exponent.val) else rotation L ^ r.exponent.val

private theorem rotation_pow_some (n : ℕ) {x y : L} (h : (W L).Nonsingular x y) :
    ∃ h' : (W L).Nonsingular ((2 : L) ^ n * x) y,
      (rotation L ^ n) (Affine.Point.some x y h) = Affine.Point.some ((2 : L) ^ n * x) y h' := by
  induction n with
  | zero =>
    refine ⟨by simpa using h, ?_⟩
    rw [pow_zero]
    change Affine.Point.some x y h = _
    simp only [Affine.Point.some.injEq, pow_zero, one_mul, and_self]
  | succ n ih =>
    obtain ⟨h', he⟩ := ih
    have hx : (2 : L) * (2 ^ n * x) = 2 ^ (n + 1) * x := by
      rw [pow_succ']
      ring
    refine ⟨by simpa only [hx] using scaledNonsingular L _ _ h', ?_⟩
    rw [pow_succ']
    change rotation L ((rotation L ^ n) (Affine.Point.some x y h)) = _
    rw [he, rotation_some, Affine.Point.some.injEq]
    exact ⟨hx, rfl⟩

private theorem ratio_pow (A : ZMod 7) (hA : A ≠ 0) :
    (a L (ratio A)) ^ 6 = 1 := by
  simpa only [map_pow, map_one] using congrArg (algebraMap (ZMod 7) L) (row_parameters A hA).2.1

private theorem ratio_ne_zero (A : ZMod 7) (hA : A ≠ 0) : a L (ratio A) ≠ 0 := by
  intro h
  have he := ratio_pow L A hA
  rw [h, zero_pow (by decide : (6 : ℕ) ≠ 0)] at he
  exact zero_ne_one he

private theorem ratio_scale (A : ZMod 7) (hA : A ≠ 0) :
    (a L (ratio A)) ^ 6 * a L 5 = a L 5 := by rw [ratio_pow L A hA, one_mul]

private theorem scale_is_signed_rotation (A : ZMod 7) (hA : A ≠ 0) (P : Points L) :
    scale (ratio_ne_zero L A hA) (ratio_scale L A hA) (disc L 5 (by decide)) (ordinaryEquiv L P) =
      ordinaryEquiv L (signedRotation L (row A) P) := by
  cases P with
  | zero =>
    change scale (ratio_ne_zero L A hA) (ratio_scale L A hA) (disc L 5 (by decide)) (ordinaryEquiv L 0) =
      ordinaryEquiv L (signedRotation L (row A) 0)
    simp only [map_zero]
  | some x y h =>
    have hX : (a L (ratio A)) ^ 2 = (2 : L) ^ (row A).exponent.val := by
      simpa only [map_pow, map_ofNat] using
        congrArg (algebraMap (ZMod 7) L) (row_parameters A hA).2.2.1
    obtain ⟨hR, eR⟩ := rotation_pow_some L (row A).exponent.val h
    rw [ordinaryEquiv_some L h, scale_some]
    cases hn : (row A).negate
    · have hY₀ : ratio A ^ 3 = 1 := by simpa [hn] using (row_parameters A hA).2.2.2.1
      have hY : (a L (ratio A)) ^ 3 = 1 := by
        simpa only [map_pow, map_one] using congrArg (algebraMap (ZMod 7) L) hY₀
      rw [show signedRotation L (row A) = rotation L ^ (row A).exponent.val by
        simp [signedRotation, hn]]
      rw [eR, ordinaryEquiv_some, Affine.Point.some.injEq]
      exact ⟨by rw [hX], by rw [hY, one_mul]⟩
    · have hY₀ : ratio A ^ 3 = -1 := by simpa [hn] using (row_parameters A hA).2.2.2.1
      have hY : (a L (ratio A)) ^ 3 = -1 := by
        simpa only [map_pow, map_neg, map_one] using congrArg (algebraMap (ZMod 7) L) hY₀
      rw [show signedRotation L (row A) = -(rotation L ^ (row A).exponent.val) by
        simp [signedRotation, hn]]
      change Affine.Point.some _ _ _ = ordinaryEquiv L (-((rotation L ^ (row A).exponent.val)
        (Affine.Point.some x y h)))
      rw [eR, Affine.Point.neg_some, ordinaryEquiv_some, Affine.Point.some.injEq]
      exact ⟨by rw [hX], by simp [hY, ordinaryCurve, Affine.negY]⟩

/-- Each native seventh-power map is the tabled sign and rotation of the reference action. -/
theorem exists_conjugacy (A : ZMod 7) (hA : A ≠ 0) :
    ∃ e : Points L ≃+ (Curve (a L A)).Point, ∀ P : Points L,
      nativeMap (ZMod 7) L (g L) A (e P) =
        e (signedRotation L (row A) (nativeFrobenius L P)) := by
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (a L (ratio A)) (by decide : 0 < (6 : ℕ))
  have hu₀ : u ≠ 0 := by
    intro he
    exact ratio_ne_zero L A hA (by simpa [he] using hu.symm)
  have hAB : u ^ 6 * a L 5 = a L A := by
    rw [hu, ← map_mul, (row_parameters A hA).1]
  have hgu : g L u = u * a L (ratio A) := by
    change u ^ Fintype.card (ZMod 7) = _
    rw [ZMod.card, show (7 : ℕ) = 6 + 1 by decide, pow_add, pow_one, hu, mul_comm]
  let e₀ := ordinaryEquiv L
  let e₁ := scaleEquiv hu₀ hAB (disc L 5 (by decide)) (disc L A hA)
  refine ⟨e₀.trans e₁, fun P => ?_⟩
  change nativeMap (ZMod 7) L (g L) A (e₁ (e₀ P)) =
    e₁ (e₀ (signedRotation L (row A) (nativeFrobenius L P)))
  have he := nativeMap_scale (g L) hu₀ (ratio_ne_zero L A hA) hAB (ratio_scale L A hA)
    (disc L 5 (by decide)) (disc L A hA) hgu (e₀ P)
  change nativeMap (ZMod 7) L (g L) A (e₁ (e₀ P)) =
    e₁ (scale (ratio_ne_zero L A hA) (ratio_scale L A hA) (disc L 5 (by decide))
      (nativeMap (ZMod 7) L (g L) 5 (ordinaryEquiv L P))) at he
  rw [equiv_frobenius, scale_is_signed_rotation L A hA] at he
  exact he

end
end ManuscriptAudit.Paper5OrdinarySevenTwistGeometry

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper5OrdinarySevenTwistGeometry.exists_conjugacy
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
