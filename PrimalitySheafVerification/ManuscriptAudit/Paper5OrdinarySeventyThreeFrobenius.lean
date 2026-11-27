import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.CubicExecutableCoordinateChain
import PrimalitySheafVerification.ManuscriptAudit.CubicCoordinateChainFrobenius

/-! The exact native prime-field Frobenius for the printed p=73 cubic. -/

namespace ManuscriptAudit.Paper5OrdinarySeventyThreeFrobenius

open Polynomial WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate CubicThreeTorsionCard
open CubicCoordinateChain CubicCoordinateChainFrobenius CubicExecutableCoordinateChain CubicExecutableFractions
open CubicFrobeniusScaling

noncomputable section

local instance : Fact (Nat.Prime 73) := ⟨by decide⟩

private abbrev CF := CoefficientFraction (ZMod 73)

private def m2 : CF := ⟨[0, -35], [1, 1]⟩
private def u2 : CF := ⟨[-2, -18], [1, 1]⟩
private def v2 : CF := ⟨[-1, -34, -9], [1, 2, 1]⟩
private def m4 : CF := ⟨[0, -25, -12, 19], [-8, 12, 21, 1]⟩
private def u4 : CF := ⟨[-36, -30, 33, -35, -34, 32], [-9, 36, -9, -14, -32, 1]⟩
private def v4 : CF := ⟨[-1, -26, -23, 4, 2, 31, 32, 1, 8], [-1, -31, 23, 21, 8, 35, -17, -11, 1]⟩
private def m8 : CF := ⟨[0, 24, -33, -3, 10, 3, 1, 1, 21, 34, 30,
    -27], [1, -12, 27, 30, -14, 7, 2, 10, -19, -27, 12,
    1]⟩
private def u8 : CF := ⟨[-8, -17, -10, -21, 20, 19, 2, 30, 10, 29, -31,
    -18, 13, -20, 17, -27, -33, -27, 35, 25, -35, 8], [1, -25, 4, -8, -11, 10, -30, -22, 30, 33, -13,
    16, 29, 34, -7, 24, 5, 24, -23, -6, 23, 1]⟩
private def v8 : CF := ⟨[-1, -35, -13, -23, 11, 35, -27, 15, -34, 33, 17,
    13, 16, -7, 3, 11, -12, -13, 14, -13, 20, 1,
    18, 32, 16, 33, 12, 19, -6, -5, 24, 35, 1], [1, 36, -34, 29, 13, -35, 33, 13, -14, -33, 10,
    -36, 25, 23, 20, -1, 13, -21, -11, -19, 23, 1,
    18, 32, 16, 33, 12, 19, -6, -5, 24, 35, 1]⟩
private def mF : CF := ⟨[0, 36, -21, -32, 2, 6, 33, -14, 20, 14, 31,
    12, -35, 33, -27, 10, 34, 28, -33, -27, 15, -13,
    25, -1], [1, -12, 27, 30, -14, 7, 2, 10, -19, -27, 12,
    1]⟩

private def targetX : CF := CoefficientFraction.polynomial (CubicCoefficientArithmetic.pow [0, 1] 24)
private def targetY : CF := CoefficientFraction.polynomial (CubicCoefficientArithmetic.pow [1, 1] 36)

set_option maxRecDepth 60000
set_option maxHeartbeats 4500000

private def step2 : Program 1 64 (.double .identity) u2 v2 :=
  .double (m := m2) .identity (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private def step4 : Program 1 64 (.double (.double .identity)) u4 v4 :=
  .double (m := m4) step2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private def step8 : Program 1 64 (.double (.double (.double .identity))) u8 v8 :=
  .double (m := m8) step4 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private def term : Term := .add (.neg .identity) (.rotate (.double (.double (.double .identity))))

private def checked : Program 1 64 term targetX targetY :=
  .add (m := mF) (.neg .identity) (.rotate step8) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private theorem targetX_eq : targetX.toFraction =
    CubicFractionCertificates.Fraction.polynomial (X ^ 24) := by
  simp [targetX, CubicCoefficientArithmetic.expand]

private theorem targetY_eq : targetY.toFraction =
    CubicFractionCertificates.Fraction.polynomial ((X + C (1 : ZMod 73)) ^ 36) := by
  simp [targetY, CubicCoefficientArithmetic.expand, add_comm]

variable (L : Type*) [Field L] [Algebra (ZMod 73) L] [IsAlgClosed L] [DecidableEq L]

abbrev a : L := algebraMap (ZMod 73) L (1 : ZMod 73)
abbrev Points := (Curve (a L)).Point

theorem two_ne_zero : (2 : L) ≠ 0 := by
  simpa only [map_ofNat] using
    (map_ne_zero (algebraMap (ZMod 73) L)).mpr (by decide : (2 : ZMod 73) ≠ 0)

theorem three_ne_zero : (3 : L) ≠ 0 := by
  simpa only [map_ofNat] using
    (map_ne_zero (algebraMap (ZMod 73) L)).mpr (by decide : (3 : ZMod 73) ≠ 0)

theorem cube_rotation : (algebraMap (ZMod 73) L (64 : ZMod 73)) ^ 3 = 1 := by
  simpa only [map_pow, map_one] using congrArg (algebraMap (ZMod 73) L)
    (by decide : (64 : ZMod 73) ^ 3 = 1)

theorem rotation_ne_one : algebraMap (ZMod 73) L (64 : ZMod 73) ≠ 1 := by
  intro h
  exact (by decide : (64 : ZMod 73) ≠ 1)
    ((algebraMap (ZMod 73) L).injective (h.trans (map_one (algebraMap (ZMod 73) L)).symm))

theorem discriminant_ne_zero : (shortCubic (0 : L) (a L)).Δ ≠ 0 :=
  shortCubic_discriminant_ne_zero (two_ne_zero L) (three_ne_zero L) (by simp [a])

def rotation : AddMonoid.End (Points L) :=
  CubicCubeRotation.rotate (algebraMap (ZMod 73) L (64 : ZMod 73))
    (cube_rotation L) (discriminant_ne_zero L)

def nativeFrobenius : AddMonoid.End (Points L) :=
  nativeMap (ZMod 73) L (FiniteField.frobeniusAlgHom (ZMod 73) L) 1

theorem native_eq_rotation : nativeFrobenius L = -((1 : ℕ) • (1 : AddMonoid.End (Points L))) + (8 : ℕ) • rotation L := by
  have h := compiles checked
  rw [targetX_eq, targetY_eq] at h
  obtain ⟨chain, hGuard⟩ := h
  have hEq := native_eq_of_chain (p := 73) (L := L)
    (by decide : 73 = 3 * 24 + 1) (by decide : 73 = 2 * 36 + 1)
    (two_ne_zero L) (cube_rotation L) (discriminant_ne_zero L) chain hGuard
  change nativeFrobenius L = term.hom (rotation L) at hEq
  refine hEq.trans ?_
  apply AddMonoidHom.ext
  intro P
  change (-(P)) + rotation L (((2 : ℕ) • (((2 : ℕ) • (((2 : ℕ) • (P))))))) = -((1 : ℕ) • P) + (8 : ℕ) • rotation L P
  simp only [map_add, map_nsmul, map_neg]
  abel

end
end ManuscriptAudit.Paper5OrdinarySeventyThreeFrobenius

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper5OrdinarySeventyThreeFrobenius.native_eq_rotation
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
