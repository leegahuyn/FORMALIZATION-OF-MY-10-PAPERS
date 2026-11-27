import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicCofiniteHom
import PrimalitySheafVerification.ManuscriptAudit.CubicFrobeniusScaling
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryThirtyOneCoordinates

/-! The native thirty-one Frobenius is 1+6ρ on the whole geometric point group. -/

namespace ManuscriptAudit.Paper5OrdinaryThirtyOneFrobenius

open WeierstrassCurve CubicThreeTorsionOrdinate CubicCofiniteHom CubicFrobeniusScaling
open CubicPolynomialGuard Paper5OrdinaryThirtyOneCertificates Paper5OrdinaryThirtyOneCoordinates

noncomputable section

local instance : Fact (Nat.Prime 31) := ⟨by decide⟩

variable (L : Type*) [Field L] [Algebra (ZMod 31) L] [CharP L 31] [IsAlgClosed L] [DecidableEq L]

def nativeFrobenius : AddMonoid.End (Points L) :=
  nativeMap (ZMod 31) L (FiniteField.frobeniusAlgHom (ZMod 31) L) 1

theorem native_eq_rotation : nativeFrobenius L = 1 + (6 : ℕ) • rotation L := by
  apply cubicHom_ext (discriminant_ne_zero L) _ _ (exceptional_finite excluded excluded_nonzero)
  intro x y hP hxGood
  let g := FiniteField.frobeniusAlgHom (ZMod 31) L
  have hg (v : L) : g v = v ^ 31 := by
    change v ^ Fintype.card (ZMod 31) = _
    rw [ZMod.card]
  obtain ⟨hF, eF⟩ := nativeMap_some (ZMod 31) L g 1 hP
  obtain ⟨hC, eC⟩ := computed_some L hP hxGood
  change nativeFrobenius L (Affine.Point.some x y hP) =
    (Affine.Point.some x y hP : Points L) + (6 : ℕ) • rotation L (Affine.Point.some x y hP)
  have eF' : nativeFrobenius L (Affine.Point.some x y hP) = Affine.Point.some (g x) (g y) hF := eF
  rw [eF', eC, Affine.Point.some.injEq]
  exact ⟨hg x, hg y⟩

end
end ManuscriptAudit.Paper5OrdinaryThirtyOneFrobenius

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper5OrdinaryThirtyOneFrobenius.native_eq_rotation
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
