import Lean.Util.CollectAxioms
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.CubicFrobeniusScaling
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryNineteenFrobenius
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryNineteenTwistParameters

/-! A sixth-root change of variables gives the actual Frobenius conjugacies over F₁₉. -/

namespace ManuscriptAudit.Paper5OrdinaryNineteenTwistGeometry

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate CubicThreeTorsionCard
open CubicFrobeniusScaling CubicPointScaling CubicNonsplitFrobeniusTrace CubicTriplingCoordinates
open Paper5OrdinaryNineteenAlgebra Paper5OrdinaryNineteenCoordinates
open Paper5OrdinaryNineteenFrobenius Paper5OrdinaryNineteenTwistParameters

noncomputable section

local instance : Fact (Nat.Prime 19) := ⟨by decide⟩

variable (L : Type*) [Field L] [Algebra (ZMod 19) L] [CharP L 19] [IsAlgClosed L] [DecidableEq L]

private abbrev a (x : ZMod 19) := algebraMap (ZMod 19) L x
private abbrev g := FiniteField.frobeniusAlgHom (ZMod 19) L

def signedRotation (r : Row) : AddMonoid.End (Points L) :=
  if r.negate then -(rotation L ^ r.exponent.val) else rotation L ^ r.exponent.val

private theorem rotation_pow_some (n : ℕ) {x y : L} (h : (Curve (1 : L)).Nonsingular x y) :
    ∃ h' : (Curve (1 : L)).Nonsingular ((7 : L) ^ n * x) y,
      (rotation L ^ n) (Affine.Point.some x y h) = Affine.Point.some ((7 : L) ^ n * x) y h' := by
  induction n with
  | zero =>
    refine ⟨by simpa using h, ?_⟩
    rw [pow_zero]
    change Affine.Point.some x y h = _
    simp only [Affine.Point.some.injEq, pow_zero, one_mul, and_self]
  | succ n ih =>
    obtain ⟨h', he⟩ := ih
    obtain ⟨h'', he'⟩ := rotation_some L h'
    have hx : (7 : L) * ((7 : L) ^ n * x) = (7 : L) ^ (n + 1) * x := by
      rw [pow_succ']
      ring
    refine ⟨by simpa only [hx] using h'', ?_⟩
    rw [pow_succ']
    change rotation L ((rotation L ^ n) (Affine.Point.some x y h)) = _
    rw [he, he', Affine.Point.some.injEq]
    exact ⟨hx, rfl⟩

private theorem signedRotation_some (r : Row) {x y : L} (h : (Curve (1 : L)).Nonsingular x y) :
    ∃ h' : (Curve (1 : L)).Nonsingular ((7 : L) ^ r.exponent.val * x) (if r.negate then -y else y),
      signedRotation L r (Affine.Point.some x y h) =
        Affine.Point.some ((7 : L) ^ r.exponent.val * x) (if r.negate then -y else y) h' := by
  obtain ⟨hR, eR⟩ := rotation_pow_some L r.exponent.val h
  cases hNeg : r.negate
  · refine ⟨by simpa [hNeg] using hR, ?_⟩
    simpa [signedRotation, hNeg] using eR
  · have hN := (Affine.nonsingular_neg ..).mpr hR
    refine ⟨by simpa [hNeg, negY_eq] using hN, ?_⟩
    rw [show signedRotation L r = -(rotation L ^ r.exponent.val) by simp [signedRotation, hNeg]]
    change -((rotation L ^ r.exponent.val) (Affine.Point.some x y h)) = _
    rw [eR, Affine.Point.neg_some, Affine.Point.some.injEq]
    exact ⟨rfl, by simp [hNeg, negY_eq]⟩

private theorem disc (A : ZMod 19) (hA : A ≠ 0) :
    (shortCubic (0 : L) (a L A)).Δ ≠ 0 :=
  shortCubic_discriminant_ne_zero (numeral_ne_zero 2 (by decide))
    (numeral_ne_zero 3 (by decide)) ((map_ne_zero (algebraMap (ZMod 19) L)).mpr hA)

set_option maxHeartbeats 1200000 in
theorem exists_conjugacy (A : ZMod 19) (hA : A ≠ 0) :
    ∃ e : Points L ≃+ (Curve (a L A)).Point, ∀ P : Points L,
      nativeMap (ZMod 19) L (g L) A (e P) =
        e (signedRotation L (row A) (nativeFrobenius L P)) := by
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (a L A) (by decide : 0 < (6 : ℕ))
  have hu₀ : u ≠ 0 := by
    intro he
    exact ((map_ne_zero (algebraMap (ZMod 19) L)).mpr hA) (by simpa [he] using hu.symm)
  have hAB : u ^ 6 * (1 : L) = a L A := by simpa only [mul_one] using hu
  have huF : g L u = u * a L (ratio A) := by
    change u ^ Fintype.card (ZMod 19) = _
    rw [ZMod.card, show (19 : ℕ) = 6 * 3 + 1 by decide, pow_add, pow_mul, pow_one, hu]
    simp only [ratio, map_pow]
    ring
  let e := scaleEquiv hu₀ hAB (discriminant_ne_zero L) (disc L A hA)
  refine ⟨e, fun P => ?_⟩
  cases P with
  | zero =>
    change nativeMap (ZMod 19) L (g L) A (e 0) =
      e (signedRotation L (row A) (nativeFrobenius L 0))
    simp only [map_zero]
  | some x y h =>
    let hQ := scaled_nonsingular hAB (disc L A hA) h
    have eQ : e (Affine.Point.some x y h) = Affine.Point.some (u ^ 2 * x) (u ^ 3 * y) hQ := rfl
    obtain ⟨hAF, eAF⟩ := nativeMap_some (ZMod 19) L (g L) A hQ
    obtain ⟨hF, eF₀⟩ := pointMapAt_some (ZMod 19) L (Curve (1 : ZMod 19)) (Curve (1 : L))
      (ordinary_baseChange L) (g L) x y h
    have eF : nativeFrobenius L (Affine.Point.some x y h) =
        Affine.Point.some (g L x) (g L y) hF := eF₀
    obtain ⟨hR, eR⟩ := signedRotation_some L (row A) hF
    have hX : (a L (ratio A)) ^ 2 = (7 : L) ^ (row A).exponent.val := by
      simpa only [map_pow, map_ofNat] using congrArg (algebraMap (ZMod 19) L) (row_parameters A hA).2.1
    have hY : (a L (ratio A)) ^ 3 * g L y = (if (row A).negate then -(g L y) else g L y) := by
      cases hn : (row A).negate
      · have hy : ratio A ^ 3 = 1 := by simpa [hn] using (row_parameters A hA).2.2.1
        have hy' : (a L (ratio A)) ^ 3 = 1 := by
          simpa only [map_pow, map_one] using congrArg (algebraMap (ZMod 19) L) hy
        simp [hn, hy']
      · have hy : ratio A ^ 3 = -1 := by simpa [hn] using (row_parameters A hA).2.2.1
        have hy' : (a L (ratio A)) ^ 3 = -1 := by
          simpa only [map_pow, map_neg, map_one] using congrArg (algebraMap (ZMod 19) L) hy
        simp [hn, hy']
    rw [eQ, eAF, eF, eR]
    dsimp only [e]
    rw [scaleEquiv_some, Affine.Point.some.injEq]
    constructor
    · rw [map_mul, map_pow, huF, mul_pow, hX]
      ring
    · rw [map_mul, map_pow, huF, mul_pow]
      calc
        _ = u ^ 3 * ((a L (ratio A)) ^ 3 * g L y) := by ring
        _ = _ := congrArg (fun t : L => u ^ 3 * t) hY

end
end ManuscriptAudit.Paper5OrdinaryNineteenTwistGeometry

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper5OrdinaryNineteenTwistGeometry.exists_conjugacy
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
