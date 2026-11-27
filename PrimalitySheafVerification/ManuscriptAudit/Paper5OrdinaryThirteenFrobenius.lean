import Lean.Util.CollectAxioms
import Mathlib.Algebra.Polynomial.Roots
import PrimalitySheafVerification.ManuscriptAudit.CubicCofiniteHom
import PrimalitySheafVerification.ManuscriptAudit.CubicNonsplitFrobeniusTrace
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryThirteenCoordinates

/-! The actual ordinary Frobenius on y²=x³+1 in characteristic thirteen is −1−4ρ. -/

namespace ManuscriptAudit.Paper5OrdinaryThirteenFrobenius

open Polynomial WeierstrassCurve CubicThreeTorsionOrdinate CubicNonsplitFrobeniusTrace
open CubicCofiniteHom Paper5OrdinaryThirteenCoordinates Paper5OrdinaryThirteenAlgebra

noncomputable section

local instance : Fact (Nat.Prime 13) := ⟨by decide⟩

variable (L : Type*) [Field L] [Algebra (ZMod 13) L] [CharP L 13] [IsAlgClosed L] [DecidableEq L]

theorem ordinary_baseChange :
    (Curve (1 : ZMod 13)).baseChange L = Curve (1 : L) := by
  simpa only [map_one] using centered_baseChange (ZMod 13) L (1 : ZMod 13)

def nativeFrobenius : AddMonoid.End (Points L) :=
  pointMapAt (ZMod 13) L (Curve (1 : ZMod 13)) (Curve (1 : L)) (ordinary_baseChange L)
    (FiniteField.frobeniusAlgHom (ZMod 13) L)

def candidate : AddMonoid.End (Points L) :=
  -(rotation L * ((3 : ℕ) • 1 - rotation L))

private def exceptional : Set L := {x | x * (x ^ 3 + 1) * (x ^ 3 + 4) * (x ^ 3 + 2) = 0}

private theorem exceptional_finite : (exceptional L).Finite := by
  let p : L[X] := X * (X ^ 3 + C 1) * (X ^ 3 + C 4) * (X ^ 3 + C 2)
  have hM (c : L) : (X ^ 3 + C c).Monic := monic_X_pow_add_C c (by decide)
  have hp : p.Monic := ((monic_X.mul (hM 1)).mul (hM 4)).mul (hM 2)
  refine (finite_setOf_isRoot hp.ne_zero).subset ?_
  intro x hx
  change p.eval x = 0
  simpa only [p, eval_mul, eval_add, eval_pow, eval_C, eval_X] using hx

set_option maxHeartbeats 1000000 in
/-- Frobenius equals −ρ(3−ρ) on every native geometric point, including exceptional fibers. -/
theorem native_factor : nativeFrobenius L = candidate L := by
  apply cubicHom_ext (discriminant_ne_zero L) _ _ (exceptional_finite L)
  intro x y hP hxBad
  have hProd : x * (x ^ 3 + 1) * (x ^ 3 + 4) * (x ^ 3 + 2) ≠ 0 := hxBad
  have hx : x ≠ 0 := fun h => hProd (by simp [h])
  have h1 : x ^ 3 + 1 ≠ 0 := fun h => hProd (by simp [h])
  have h4 : x ^ 3 + 4 ≠ 0 := fun h => hProd (by simp [h])
  have h2 : x ^ 3 + 2 ≠ 0 := fun h => hProd (by simp [h])
  have hy : y ≠ 0 := by
    intro hy
    apply h1
    simpa only [hy, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
      ((nonsingular_iff (discriminant_ne_zero L) _ _).mp hP).symm
  let g := FiniteField.frobeniusAlgHom (ZMod 13) L
  have hg (x : L) : g x = x ^ 13 := by
    change x ^ Fintype.card (ZMod 13) = _
    rw [ZMod.card]
  obtain ⟨hF, eF⟩ := pointMapAt_some (ZMod 13) L (Curve (1 : ZMod 13)) (Curve (1 : L))
    (ordinary_baseChange L) g x y hP
  change nativeFrobenius L (Affine.Point.some x y hP) = _ at eF
  obtain ⟨hH, eH⟩ := three_sub_rotation_some L hP hx hy h4 h2
  rw [eF]
  change Affine.Point.some (g x) (g y) hF =
    -rotation L ((3 : ℕ) • (Affine.Point.some x y hP : Points L) - rotation L (Affine.Point.some x y hP))
  rw [eH]
  obtain ⟨hR, eR⟩ := rotation_some L hH
  rw [eR, Affine.Point.neg_some, Affine.Point.some.injEq, hg, hg]
  constructor
  · linear_combination (-2 * x ^ 13) * (thirteen_zero (K := L))
  · rw [CubicTriplingCoordinates.negY_eq, neg_neg]

/-- Frobenius has exact integral rotation coefficients (−1,−4). -/
theorem native_eq_rotation :
    nativeFrobenius L = -(1 : AddMonoid.End (Points L)) - (4 : ℕ) • rotation L := by
  apply AddMonoidHom.ext
  intro P
  have he := congrArg (fun f : AddMonoid.End (Points L) => f P) (native_factor L)
  change nativeFrobenius L P = -rotation L ((3 : ℕ) • P - rotation L P) at he
  change nativeFrobenius L P = -P - (4 : ℕ) • rotation L P
  rw [he, map_sub, map_nsmul, rotation_sq]
  abel

end
end ManuscriptAudit.Paper5OrdinaryThirteenFrobenius

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5OrdinaryThirteenFrobenius.native_factor,
      ``ManuscriptAudit.Paper5OrdinaryThirteenFrobenius.native_eq_rotation] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
