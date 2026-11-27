import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.CubicExecutableCoordinateChain
import PrimalitySheafVerification.ManuscriptAudit.CubicCoordinateChainFrobenius

/-! The exact native prime-field Frobenius for the printed p=43 cubic. -/

namespace ManuscriptAudit.Paper5OrdinaryFortyThreeFrobenius

open Polynomial WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate CubicThreeTorsionCard
open CubicCoordinateChain CubicCoordinateChainFrobenius CubicExecutableCoordinateChain CubicExecutableFractions
open CubicFrobeniusScaling

noncomputable section

local instance : Fact (Nat.Prime 43) := ⟨by decide⟩

private abbrev CF := CoefficientFraction (ZMod 43)

private def m2 : CF := ⟨[0, -20], [1, 1]⟩
private def u2 : CF := ⟨[-2, 11], [1, 1]⟩
private def v2 : CF := ⟨[-1, -19, -16], [1, 2, 1]⟩
private def m3 : CF := ⟨[17, -15, -6], [4, 5, 1]⟩
private def u3 : CF := ⟨[-12, -9, 18, -19], [0, 16, 8, 1]⟩
private def v3 : CF := ⟨[-11, 20, -18, -3, 8], [0, 21, 5, 12, 1]⟩
private def mk : CF := ⟨[-16, 19, -4, 14, 12, -10, -21], [16, -13, -14, -21, 16, 10, 1]⟩
private def uk : CF := ⟨[-5, -15, -15, 21, -16, 3, -6, 15, 8, 1, -10, -15, 6], [0, -2, 16, 6, -13, 20, -1, -19, -13, -7, -16, 19, 1]⟩
private def vk : CF := ⟨[-2, -9, -3, -4, 11, 4, 1, -14, -20, -2, 6, -10, -1, 11, -21, -13, 18, -14, 1], [0, 11, -19, 2, 5, -6, 16, -1, 17, -19, -15, -13, -1, 11, -21, -13, 18, -14, 1]⟩
private def mF : CF := ⟨[-11, 9, 6, -18, 0, 0, 7, -16, -12, -2, -4, -6, 12, -1], [16, -13, -14, -21, 16, 10, 1]⟩

private def targetX : CF := CoefficientFraction.polynomial (CubicCoefficientArithmetic.pow [0, 1] 14)
private def targetY : CF := CoefficientFraction.polynomial (CubicCoefficientArithmetic.pow [1, 1] 21)

set_option maxRecDepth 60000
set_option maxHeartbeats 4500000

private def two : Program 1 36 (.double .identity) u2 v2 :=
  .double (m := m2) .identity (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private def three : Program 1 36 (.add .identity (.double .identity)) u3 v3 :=
  .add (m := m3) .identity two (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private def lastMultiple : Program 1 36 (.double (.add .identity (.double .identity))) uk vk :=
  .double (m := mk) three (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private def term : Term := .add .identity (.neg (.rotate (.double (.add .identity (.double .identity)))))

private def checked : Program 1 36 term targetX targetY :=
  .add (m := mF) (.identity) (.neg (.rotate lastMultiple)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private theorem targetX_eq : targetX.toFraction =
    CubicFractionCertificates.Fraction.polynomial (X ^ 14) := by
  simp [targetX, CubicCoefficientArithmetic.expand]

private theorem targetY_eq : targetY.toFraction =
    CubicFractionCertificates.Fraction.polynomial ((X + C (1 : ZMod 43)) ^ 21) := by
  simp [targetY, CubicCoefficientArithmetic.expand, add_comm]

variable (L : Type*) [Field L] [Algebra (ZMod 43) L] [IsAlgClosed L] [DecidableEq L]

abbrev a : L := algebraMap (ZMod 43) L (1 : ZMod 43)
abbrev Points := (Curve (a L)).Point

theorem two_ne_zero : (2 : L) ≠ 0 := by
  simpa only [map_ofNat] using
    (map_ne_zero (algebraMap (ZMod 43) L)).mpr (by decide : (2 : ZMod 43) ≠ 0)

theorem three_ne_zero : (3 : L) ≠ 0 := by
  simpa only [map_ofNat] using
    (map_ne_zero (algebraMap (ZMod 43) L)).mpr (by decide : (3 : ZMod 43) ≠ 0)

theorem cube_rotation : (algebraMap (ZMod 43) L (36 : ZMod 43)) ^ 3 = 1 := by
  simpa only [map_pow, map_one] using congrArg (algebraMap (ZMod 43) L)
    (by decide : (36 : ZMod 43) ^ 3 = 1)

theorem rotation_ne_one : algebraMap (ZMod 43) L (36 : ZMod 43) ≠ 1 := by
  intro h
  exact (by decide : (36 : ZMod 43) ≠ 1)
    ((algebraMap (ZMod 43) L).injective (h.trans (map_one (algebraMap (ZMod 43) L)).symm))

theorem discriminant_ne_zero : (shortCubic (0 : L) (a L)).Δ ≠ 0 :=
  shortCubic_discriminant_ne_zero (two_ne_zero L) (three_ne_zero L) (by simp [a])

def rotation : AddMonoid.End (Points L) :=
  CubicCubeRotation.rotate (algebraMap (ZMod 43) L (36 : ZMod 43))
    (cube_rotation L) (discriminant_ne_zero L)

def nativeFrobenius : AddMonoid.End (Points L) :=
  nativeMap (ZMod 43) L (FiniteField.frobeniusAlgHom (ZMod 43) L) 1

theorem native_eq_rotation : nativeFrobenius L = (1 : AddMonoid.End (Points L)) - (6 : ℕ) • rotation L := by
  have h := compiles checked
  rw [targetX_eq, targetY_eq] at h
  obtain ⟨chain, hGuard⟩ := h
  have hEq := native_eq_of_chain (p := 43) (L := L)
    (by decide : 43 = 3 * 14 + 1) (by decide : 43 = 2 * 21 + 1)
    (two_ne_zero L) (cube_rotation L) (discriminant_ne_zero L) chain hGuard
  change nativeFrobenius L = term.hom (rotation L) at hEq
  refine hEq.trans ?_
  apply AddMonoidHom.ext
  intro P
  change P + -(rotation L ((2 : ℕ) • (P + (2 : ℕ) • P))) = P - (6 : ℕ) • rotation L P
  simp only [map_add, map_nsmul]
  abel

end
end ManuscriptAudit.Paper5OrdinaryFortyThreeFrobenius

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper5OrdinaryFortyThreeFrobenius.native_eq_rotation
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
