import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicNonsplitFrobeniusTrace
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinarySevenFrobeniusCoordinates

/-! The actual ordinary characteristic-seven Frobenius is the endomorphism −1−3ρ. -/

namespace ManuscriptAudit.Paper5OrdinarySevenFrobenius

open WeierstrassCurve CubicNonsplitFrobeniusTrace
open Paper5OrdinarySeven Paper5OrdinarySevenGeometry Paper5OrdinarySevenFrobeniusCoordinates

noncomputable section

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

variable (L : Type*) [Field L] [Algebra (ZMod 7) L] [CharP L 7] [DecidableEq L]

private abbrev W₀ := (ordinaryCurve (ZMod 7)).toAffine
private abbrev W := (ordinaryCurve L).toAffine

theorem ordinary_baseChange : W₀.baseChange L = W L := by
  simp [W₀, W, ordinaryCurve, WeierstrassCurve.baseChange, WeierstrassCurve.map, map_ofNat]

def nativeFrobenius : AddMonoid.End (Points L) :=
  pointMapAt (ZMod 7) L W₀ (W L) (ordinary_baseChange L) (FiniteField.frobeniusAlgHom (ZMod 7) L)

set_option maxHeartbeats 1200000 in
/-- The native geometric map is minus the rotation of the actual endomorphism 2−ρ. -/
theorem native_factor (P : Points L) :
    nativeFrobenius L P = -rotation L ((2 : ℕ) • P - rotation L P) := by
  let g := FiniteField.frobeniusAlgHom (ZMod 7) L
  have hg (x : L) : g x = x ^ 7 := by
    change x ^ Fintype.card (ZMod 7) = _
    rw [ZMod.card]
  cases P with
  | zero =>
    change nativeFrobenius L 0 = -rotation L ((2 : ℕ) • 0 - rotation L 0)
    simp only [map_zero, nsmul_zero, sub_zero, neg_zero]
  | some x y hP =>
    obtain ⟨hQ, hTwo⟩ := two_sub_rotation_coordinates L hP
    obtain ⟨hF, he⟩ := pointMapAt_some (ZMod 7) L W₀ (W L) (ordinary_baseChange L) g x y hP
    change nativeFrobenius L (Affine.Point.some x y hP) = _ at he
    rw [he, hTwo, rotation_some, Affine.Point.neg_some, Affine.Point.some.injEq, hg, hg]
    constructor
    · linear_combination (-(x ^ 7)) * seven_zero L
    · rw [negY_eq, neg_neg]

/-- The exact actual ordinary Frobenius, expressed in the native rotation algebra. -/
theorem native_eq_rotation :
    nativeFrobenius L = -(1 : AddMonoid.End (Points L)) - (3 : ℕ) • rotation L := by
  apply AddMonoidHom.ext
  intro P
  change nativeFrobenius L P = -P - (3 : ℕ) • rotation L P
  have hR : rotation L (rotation L P) = -P - rotation L P := by
    calc
      _ = (rotation L P + rotation L (rotation L P)) - rotation L P := by abel
      _ = _ := by rw [rotation_sum]
  rw [native_factor, map_sub, map_nsmul, hR]
  abel

end
end ManuscriptAudit.Paper5OrdinarySevenFrobenius

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5OrdinarySevenFrobenius.ordinary_baseChange,
      ``ManuscriptAudit.Paper5OrdinarySevenFrobenius.native_factor,
      ``ManuscriptAudit.Paper5OrdinarySevenFrobenius.native_eq_rotation] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
