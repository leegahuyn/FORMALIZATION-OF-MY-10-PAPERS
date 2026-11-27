import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.CubicExecutableCoordinateChain
import PrimalitySheafVerification.ManuscriptAudit.CubicCoordinateChainFrobenius

/-! The exact native prime-field Frobenius for the printed p=37 cubic. -/

namespace ManuscriptAudit.Paper5OrdinaryThirtySevenFrobenius

open Polynomial WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate CubicThreeTorsionCard
open CubicCoordinateChain CubicCoordinateChainFrobenius CubicExecutableCoordinateChain CubicExecutableFractions
open CubicFrobeniusScaling

noncomputable section

local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

private abbrev CF := CoefficientFraction (ZMod 37)

private def m2 : CF := ⟨[0, -17], [1, 1]⟩
private def u2 : CF := ⟨[-2, -9], [1, 1]⟩
private def v2 : CF := ⟨[-1, -16, 14], [1, 2, 1]⟩
private def m3 : CF := ⟨[15, -13, -5], [4, 5, 1]⟩
private def u3 : CF := ⟨[3, -7, 14, -4], [0, 16, 8, 1]⟩
private def v3 : CF := ⟨[-8, -5, 0, 15, 11], [0, -10, 11, 12, 1]⟩
private def mk : CF := ⟨[0, 11, -12, 10], [-8, 12, -16, 1]⟩
private def uk : CF := ⟨[-3, -7, -11, -1, 3, 7], [-10, 3, -10, 17, 4, 1]⟩
private def vk : CF := ⟨[6, 8, -13, 12, -15, 5, 8, 10, 11], [6, 4, 17, -18, 2, 17, 2, -12, 1]⟩
private def mF : CF := ⟨[-9, 12, 14, -8, -8, -6, 14, -8, 4, -6, -1], [5, 3, -15, -12, 1]⟩

private def targetX : CF := CoefficientFraction.polynomial (CubicCoefficientArithmetic.pow [0, 1] 12)
private def targetY : CF := CoefficientFraction.polynomial (CubicCoefficientArithmetic.pow [1, 1] 18)

set_option maxRecDepth 60000
set_option maxHeartbeats 4500000

private def two : Program 1 10 (.double .identity) u2 v2 :=
  .double (m := m2) .identity (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private def three : Program 1 10 (.add .identity (.double .identity)) u3 v3 :=
  .add (m := m3) .identity two (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private def lastMultiple : Program 1 10 (.double (.double .identity)) uk vk :=
  .double (m := mk) two (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private def term : Term := .add (.neg (.add .identity (.double .identity))) (.rotate (.double (.double .identity)))

private def checked : Program 1 10 term targetX targetY :=
  .add (m := mF) (.neg three) (.rotate lastMultiple) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private theorem targetX_eq : targetX.toFraction =
    CubicFractionCertificates.Fraction.polynomial (X ^ 12) := by
  simp [targetX, CubicCoefficientArithmetic.expand]

private theorem targetY_eq : targetY.toFraction =
    CubicFractionCertificates.Fraction.polynomial ((X + C (1 : ZMod 37)) ^ 18) := by
  simp [targetY, CubicCoefficientArithmetic.expand, add_comm]

variable (L : Type*) [Field L] [Algebra (ZMod 37) L] [IsAlgClosed L] [DecidableEq L]

abbrev a : L := algebraMap (ZMod 37) L (1 : ZMod 37)
abbrev Points := (Curve (a L)).Point

theorem two_ne_zero : (2 : L) ≠ 0 := by
  simpa only [map_ofNat] using
    (map_ne_zero (algebraMap (ZMod 37) L)).mpr (by decide : (2 : ZMod 37) ≠ 0)

theorem three_ne_zero : (3 : L) ≠ 0 := by
  simpa only [map_ofNat] using
    (map_ne_zero (algebraMap (ZMod 37) L)).mpr (by decide : (3 : ZMod 37) ≠ 0)

theorem cube_rotation : (algebraMap (ZMod 37) L (10 : ZMod 37)) ^ 3 = 1 := by
  simpa only [map_pow, map_one] using congrArg (algebraMap (ZMod 37) L)
    (by decide : (10 : ZMod 37) ^ 3 = 1)

theorem rotation_ne_one : algebraMap (ZMod 37) L (10 : ZMod 37) ≠ 1 := by
  intro h
  exact (by decide : (10 : ZMod 37) ≠ 1)
    ((algebraMap (ZMod 37) L).injective (h.trans (map_one (algebraMap (ZMod 37) L)).symm))

theorem discriminant_ne_zero : (shortCubic (0 : L) (a L)).Δ ≠ 0 :=
  shortCubic_discriminant_ne_zero (two_ne_zero L) (three_ne_zero L) (by simp [a])

def rotation : AddMonoid.End (Points L) :=
  CubicCubeRotation.rotate (algebraMap (ZMod 37) L (10 : ZMod 37))
    (cube_rotation L) (discriminant_ne_zero L)

def nativeFrobenius : AddMonoid.End (Points L) :=
  nativeMap (ZMod 37) L (FiniteField.frobeniusAlgHom (ZMod 37) L) 1

theorem native_eq_rotation : nativeFrobenius L = -((3 : ℕ) • (1 : AddMonoid.End (Points L))) + (4 : ℕ) • rotation L := by
  have h := compiles checked
  rw [targetX_eq, targetY_eq] at h
  obtain ⟨chain, hGuard⟩ := h
  have hEq := native_eq_of_chain (p := 37) (L := L)
    (by decide : 37 = 3 * 12 + 1) (by decide : 37 = 2 * 18 + 1)
    (two_ne_zero L) (cube_rotation L) (discriminant_ne_zero L) chain hGuard
  change nativeFrobenius L = term.hom (rotation L) at hEq
  refine hEq.trans ?_
  apply AddMonoidHom.ext
  intro P
  change -(P + (2 : ℕ) • P) + rotation L ((2 : ℕ) • ((2 : ℕ) • P)) =
    -((3 : ℕ) • P) + (4 : ℕ) • rotation L P
  simp only [map_nsmul]
  abel

end
end ManuscriptAudit.Paper5OrdinaryThirtySevenFrobenius

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper5OrdinaryThirtySevenFrobenius.native_eq_rotation
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
