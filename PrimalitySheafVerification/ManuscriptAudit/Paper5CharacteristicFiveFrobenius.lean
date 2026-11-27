import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicCharacteristicFiveMultiple
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassFrobeniusFixed

/-! The square of the actual prime-field Frobenius is multiplication by minus five. -/

namespace ManuscriptAudit.Paper5CharacteristicFiveFrobenius

open WeierstrassCurve FiniteFieldPointCount CubicTwoTorsion
open CubicThreeTorsionOrdinate CubicCharacteristicFiveDouble CubicCharacteristicFiveMultiple
open WeierstrassFrobeniusFixed

noncomputable section

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

variable (L : Type*) [Field L] [Algebra (ZMod 5) L] [DecidableEq L]

theorem centered_baseChange (A : ZMod 5) :
    (Curve A).baseChange L = Curve (algebraMap (ZMod 5) L A) := by
  simp [Curve, CubicAffine, shortCubic, WeierstrassCurve.baseChange, WeierstrassCurve.map]

private theorem five_some_on_baseChange {V W : Affine L} (he : V = W) {x y : L}
    (hP : V.Nonsingular x y)
    (hW : ∀ h : W.Nonsingular x y,
      ∃ hs : W.Nonsingular (x ^ 25) (-(y ^ 25)),
        (5 : ℕ) • (Affine.Point.some x y h : W.Point) =
          Affine.Point.some (x ^ 25) (-(y ^ 25)) hs) :
    ∃ h : V.Nonsingular (x ^ 25) (-(y ^ 25)),
      (5 : ℕ) • (Affine.Point.some x y hP : V.Point) =
        Affine.Point.some (x ^ 25) (-(y ^ 25)) h := by
  subst W
  exact hW hP

/-- Actual composition of native Frobenius with itself is the scalar endomorphism [-5]. -/
theorem frobenius_sq_eq_neg_five {A : ZMod 5} (hA : A ≠ 0)
    (P : ((Curve A).baseChange L).Point) :
    frobeniusOnPoints 5 L (Curve A) (frobeniusOnPoints 5 L (Curve A) P) = -((5 : ℕ) • P) := by
  letI : CharP L 5 := charP_of_injective_algebraMap (algebraMap (ZMod 5) L).injective 5
  let W := Curve A
  let V := W.baseChange L
  let a := algebraMap (ZMod 5) L A
  have he : V = Curve a := centered_baseChange L A
  have ha : a ≠ 0 := (map_ne_zero (algebraMap (ZMod 5) L)).mpr hA
  have hA4 : A ^ 4 = 1 := by
    simpa only [ZMod.card] using FiniteField.pow_card_sub_one_eq_one A hA
  have ha4 : a ^ 4 = 1 := by
    change (algebraMap (ZMod 5) L A) ^ 4 = 1
    rw [← map_pow, hA4, map_one]
  let f := FiniteField.frobeniusAlgHom (ZMod 5) L
  have hf (x : L) : f x = x ^ 5 := by
    change x ^ Fintype.card (ZMod 5) = x ^ 5
    rw [ZMod.card]
  have hff (x : L) : f (f x) = x ^ 25 := by
    rw [hf (f x), hf x, ← pow_mul] <;> rfl
  have hneg (x y : L) : V.negY x y = -y := by
    rw [he]
    exact CubicCharacteristicFiveDouble.negY x y
  cases P with
  | zero =>
      change frobeniusOnPoints 5 L W (frobeniusOnPoints 5 L W (0 : V.Point)) = -((5 : ℕ) • (0 : V.Point))
      simp
  | some x y hP =>
      obtain ⟨hs, hFive⟩ := five_some_on_baseChange L he hP (fun h => five_some ha ha4 h)
      apply neg_injective
      rw [neg_neg]
      change -(Affine.Point.map (W' := W) f
          (Affine.Point.map (W' := W) f (Affine.Point.some x y hP))) =
        (5 : ℕ) • Affine.Point.some x y hP
      rw [hFive, Affine.Point.map_some, Affine.Point.map_some, Affine.Point.neg_some,
        Affine.Point.some.injEq]
      exact ⟨hff x, by rw [hneg, hff y]⟩

end
end ManuscriptAudit.Paper5CharacteristicFiveFrobenius

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.Paper5CharacteristicFiveFrobenius.frobenius_sq_eq_neg_five
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
