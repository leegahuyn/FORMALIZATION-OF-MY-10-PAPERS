import Lean.Util.CollectAxioms
import Mathlib.Algebra.Polynomial.Roots
import PrimalitySheafVerification.ManuscriptAudit.CubicCofiniteHom
import PrimalitySheafVerification.ManuscriptAudit.CubicNonsplitFrobeniusTrace
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryNineteenCoordinates

/-! The actual ordinary Frobenius on y²=x³+1 in characteristic nineteen is 5+2ρ. -/

namespace ManuscriptAudit.Paper5OrdinaryNineteenFrobenius

open Polynomial WeierstrassCurve CubicThreeTorsionOrdinate CubicNonsplitFrobeniusTrace
open CubicCofiniteHom Paper5OrdinaryNineteenCoordinates Paper5OrdinaryNineteenAlgebra

noncomputable section

local instance : Fact (Nat.Prime 19) := ⟨by decide⟩

variable (L : Type*) [Field L] [Algebra (ZMod 19) L] [CharP L 19] [IsAlgClosed L] [DecidableEq L]

theorem ordinary_baseChange :
    (Curve (1 : ZMod 19)).baseChange L = Curve (1 : L) := by
  simpa only [map_one] using centered_baseChange (ZMod 19) L (1 : ZMod 19)

def nativeFrobenius : AddMonoid.End (Points L) :=
  pointMapAt (ZMod 19) L (Curve (1 : ZMod 19)) (Curve (1 : L)) (ordinary_baseChange L)
    (FiniteField.frobeniusAlgHom (ZMod 19) L)

def candidate : AddMonoid.End (Points L) :=
  (3 : ℕ) • (1 : AddMonoid.End (Points L)) - (2 : ℕ) • (rotation L * rotation L)

private def exceptional : Set L := {x | x * (x ^ 3 + 1) * (x ^ 3 + 4) * (x ^ 3 - 1) = 0}

private theorem exceptional_finite : (exceptional L).Finite := by
  let p : L[X] := X * (X ^ 3 + C 1) * (X ^ 3 + C 4) * (X ^ 3 + C (-1))
  have hM (c : L) : (X ^ 3 + C c).Monic := monic_X_pow_add_C c (by decide)
  have hp : p.Monic := ((monic_X.mul (hM 1)).mul (hM 4)).mul (hM (-1))
  refine (finite_setOf_isRoot hp.ne_zero).subset ?_
  intro x hx
  change x * (x ^ 3 + 1) * (x ^ 3 + 4) * (x ^ 3 - 1) = 0 at hx
  change p.eval x = 0
  simpa only [p, eval_mul, eval_add, eval_pow, eval_C, eval_X, sub_eq_add_neg] using hx

set_option maxHeartbeats 1000000 in
/-- Frobenius equals 3−2ρ² on every native geometric point, including exceptional fibers. -/
theorem native_factor : nativeFrobenius L = candidate L := by
  apply cubicHom_ext (discriminant_ne_zero L) _ _ (exceptional_finite L)
  intro x y hP hxBad
  have hProd : x * (x ^ 3 + 1) * (x ^ 3 + 4) * (x ^ 3 - 1) ≠ 0 := hxBad
  have hx : x ≠ 0 := fun h => hProd (by simp [h])
  have hs : x ^ 3 + 1 ≠ 0 := fun h => hProd (by simp [h])
  have h4 : x ^ 3 + 4 ≠ 0 := fun h => hProd (by simp [h])
  have h1 : x ^ 3 ≠ 1 := fun h => hProd (by simp [h])
  have hy : y ≠ 0 := by
    intro hy
    apply hs
    simpa only [hy, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
      ((nonsingular_iff (discriminant_ne_zero L) _ _).mp hP).symm
  let g := FiniteField.frobeniusAlgHom (ZMod 19) L
  have hg (x : L) : g x = x ^ 19 := by
    change x ^ Fintype.card (ZMod 19) = _
    rw [ZMod.card]
  obtain ⟨hF, eF⟩ := pointMapAt_some (ZMod 19) L (Curve (1 : ZMod 19)) (Curve (1 : L))
    (ordinary_baseChange L) g x y hP
  let P : Points L := Affine.Point.some x y hP
  change nativeFrobenius L P = candidate L P
  have eF' : nativeFrobenius L P = Affine.Point.some (g x) (g y) hF := eF
  obtain ⟨hH, eH⟩ := three_sub_two_rotation_sq_some L hP hx hy h4 h1
  have eH' : candidate L P = Affine.Point.some (x ^ 19) (y ^ 19) hH := eH
  refine eF'.trans (?_ : Affine.Point.some (g x) (g y) hF = _)
  rw [eH', Affine.Point.some.injEq]
  exact ⟨hg x, hg y⟩

/-- Frobenius has exact integral rotation coefficients (5,2). -/
theorem native_eq_rotation :
    nativeFrobenius L = (5 : ℕ) • (1 : AddMonoid.End (Points L)) + (2 : ℕ) • rotation L := by
  apply AddMonoidHom.ext
  intro P
  have he := congrArg (fun f : AddMonoid.End (Points L) => f P) (native_factor L)
  change nativeFrobenius L P = (3 : ℕ) • P - (2 : ℕ) • rotation L (rotation L P) at he
  change nativeFrobenius L P = (5 : ℕ) • P + (2 : ℕ) • rotation L P
  rw [he, rotation_sq]
  abel

end
end ManuscriptAudit.Paper5OrdinaryNineteenFrobenius

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5OrdinaryNineteenFrobenius.native_factor,
      ``ManuscriptAudit.Paper5OrdinaryNineteenFrobenius.native_eq_rotation] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
