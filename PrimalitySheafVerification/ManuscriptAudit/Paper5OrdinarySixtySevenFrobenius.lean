import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.CubicExecutableCoordinateChain
import PrimalitySheafVerification.ManuscriptAudit.CubicCoordinateChainFrobenius

/-! The exact native prime-field Frobenius for the printed p=67 cubic. -/

namespace ManuscriptAudit.Paper5OrdinarySixtySevenFrobenius

open Polynomial WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate CubicThreeTorsionCard
open CubicCoordinateChain CubicCoordinateChainFrobenius CubicExecutableCoordinateChain CubicExecutableFractions
open CubicFrobeniusScaling

noncomputable section

local instance : Fact (Nat.Prime 67) := ⟨by decide⟩

private abbrev CF := CoefficientFraction (ZMod 67)

private def m2 : CF := ⟨[0, -32], [1, 1]⟩
private def u2 : CF := ⟨[-2, 17], [1, 1]⟩
private def v2 : CF := ⟨[-1, -31, -25], [1, 2, 1]⟩
private def m4 : CF := ⟨[0, -19, -12, -16], [-8, 12, 21, 1]⟩
private def u4 : CF := ⟨[-12, -13, 8, -17, 33, 21], [-3, 12, -3, 22, -26, 1]⟩
private def v4 : CF := ⟨[24, 21, 21, -28, -26, 32, 21, -31, 22], [24, 2, -29, -30, 19, 5, 24, -5, 1]⟩
private def m8 : CF := ⟨[0, 22, 3, 3, -29, 14, -17, 20, -14, 21, -6,
    -8], [-27, -25, -22, -9, 3, -12, 2, -21, 24, 26, -20,
    1]⟩
private def u8 : CF := ⟨[-3, -27, -8, -27, -32, -23, 15, -6, 1, 18, -4,
    31, -29, 12, -5, 33, -25, 8, -6, 2, -10, 22], [-8, 18, -14, -8, -24, -20, -8, -25, -17, -29, 24,
    -24, 33, -20, -4, -12, -5, 20, -11, 24, 26, 1]⟩
private def v8 : CF := ⟨[-15, 13, 8, -21, -8, 19, -8, -13, 25, -5, 24,
    -28, 12, -33, -2, 19, 21, -16, -9, 13, 22, -9,
    0, 13, 19, 15, 31, 0, -11, -23, 16, 28, -14], [15, -18, -30, -26, 32, -16, -30, 3, -5, 14, 31,
    -2, 11, -26, 32, 7, 25, -27, 12, -7, 32, 23,
    0, 0, -28, 20, 14, 11, -7, 8, -1, 6, 1]⟩
private def m9 : CF := ⟨[-1, 10, -9, 21, 25, 1, -2, 15, 20, -14, -32,
    27, 29, -12, 11, 29, 22, -25, -14, -5, 21, -27,
    -17, -14, 28], [29, -16, 20, -15, -21, -4, 26, 2, -3, 17, 3,
    22, 7, 24, 4, 20, 26, -24, 14, -31, 15, 29,
    7, -30, 1]⟩
private def u9 : CF := ⟨[25, 18, -17, 29, -25, 18, 17, -27, -33, -21, 18,
    27, 25, 24, 15, 7, 2, 17, -8, 8, -17, 10,
    -2, 30, -9, -25, -26, 24], [0, -13, 16, 4, 3, -11, 21, 19, 17, 11, 9,
    -30, -9, -29, 11, 8, -25, 26, 21, 11, -8, 28,
    23, -21, -31, -3, -20, 1]⟩
private def v9 : CF := ⟨[9, 28, -4, 31, 15, 13, 0, -13, -11, -13, 28,
    -9, -4, -3, 7, -19, -15, 32, -22, -32, 12, 19,
    -11, -18, 25, -29, -23, -10, 19, 4, 8, 27, 25,
    20, 1, -17, 15, 23, -33, -32, 25], [0, 9, 4, -26, -17, -21, 0, -11, -25, 29, -13,
    -2, -22, 23, 13, -4, 2, -30, 0, 32, -12, -19,
    11, 13, 21, -9, 9, -29, -24, -26, -14, 6, -17,
    5, 1, -17, 15, -4, -22, -30, 1]⟩
private def mF : CF := ⟨[5, 6, -27, 22, -33, 21, -28, 17, 17, 10, 18,
    19, 5, -16, 3, 12, 14, 12, -24, 12, -12, 9,
    -2, -2, -24, -1], [-11, -30, -18, -10, -28, -17, -3, -9, -32, 24, 22,
    21, -28, -9, 1]⟩

private def targetX : CF := CoefficientFraction.polynomial (CubicCoefficientArithmetic.pow [0, 1] 22)
private def targetY : CF := CoefficientFraction.polynomial (CubicCoefficientArithmetic.pow [1, 1] 33)

set_option maxRecDepth 60000
set_option maxHeartbeats 4500000

private def step2 : Program 1 29 (.double .identity) u2 v2 :=
  .double (m := m2) .identity (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private def step4 : Program 1 29 (.double (.double .identity)) u4 v4 :=
  .double (m := m4) step2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private def step8 : Program 1 29 (.double (.double (.double .identity))) u8 v8 :=
  .double (m := m8) step4 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private def step9 : Program 1 29 (.add .identity (.double (.double (.double .identity)))) u9 v9 :=
  .add (m := m9) .identity step8 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private def term : Term := .add (.neg (.add .identity (.double (.double (.double .identity))))) (.neg (.rotate (.double .identity)))

private def checked : Program 1 29 term targetX targetY :=
  .add (m := mF) (.neg step9) (.neg (.rotate step2)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private theorem targetX_eq : targetX.toFraction =
    CubicFractionCertificates.Fraction.polynomial (X ^ 22) := by
  simp [targetX, CubicCoefficientArithmetic.expand]

private theorem targetY_eq : targetY.toFraction =
    CubicFractionCertificates.Fraction.polynomial ((X + C (1 : ZMod 67)) ^ 33) := by
  simp [targetY, CubicCoefficientArithmetic.expand, add_comm]

variable (L : Type*) [Field L] [Algebra (ZMod 67) L] [IsAlgClosed L] [DecidableEq L]

abbrev a : L := algebraMap (ZMod 67) L (1 : ZMod 67)
abbrev Points := (Curve (a L)).Point

theorem two_ne_zero : (2 : L) ≠ 0 := by
  simpa only [map_ofNat] using
    (map_ne_zero (algebraMap (ZMod 67) L)).mpr (by decide : (2 : ZMod 67) ≠ 0)

theorem three_ne_zero : (3 : L) ≠ 0 := by
  simpa only [map_ofNat] using
    (map_ne_zero (algebraMap (ZMod 67) L)).mpr (by decide : (3 : ZMod 67) ≠ 0)

theorem cube_rotation : (algebraMap (ZMod 67) L (29 : ZMod 67)) ^ 3 = 1 := by
  simpa only [map_pow, map_one] using congrArg (algebraMap (ZMod 67) L)
    (by decide : (29 : ZMod 67) ^ 3 = 1)

theorem rotation_ne_one : algebraMap (ZMod 67) L (29 : ZMod 67) ≠ 1 := by
  intro h
  exact (by decide : (29 : ZMod 67) ≠ 1)
    ((algebraMap (ZMod 67) L).injective (h.trans (map_one (algebraMap (ZMod 67) L)).symm))

theorem discriminant_ne_zero : (shortCubic (0 : L) (a L)).Δ ≠ 0 :=
  shortCubic_discriminant_ne_zero (two_ne_zero L) (three_ne_zero L) (by simp [a])

def rotation : AddMonoid.End (Points L) :=
  CubicCubeRotation.rotate (algebraMap (ZMod 67) L (29 : ZMod 67))
    (cube_rotation L) (discriminant_ne_zero L)

def nativeFrobenius : AddMonoid.End (Points L) :=
  nativeMap (ZMod 67) L (FiniteField.frobeniusAlgHom (ZMod 67) L) 1

theorem native_eq_rotation : nativeFrobenius L = -((9 : ℕ) • (1 : AddMonoid.End (Points L))) - (2 : ℕ) • rotation L := by
  have h := compiles checked
  rw [targetX_eq, targetY_eq] at h
  obtain ⟨chain, hGuard⟩ := h
  have hEq := native_eq_of_chain (p := 67) (L := L)
    (by decide : 67 = 3 * 22 + 1) (by decide : 67 = 2 * 33 + 1)
    (two_ne_zero L) (cube_rotation L) (discriminant_ne_zero L) chain hGuard
  change nativeFrobenius L = term.hom (rotation L) at hEq
  refine hEq.trans ?_
  apply AddMonoidHom.ext
  intro P
  change (-((P + ((2 : ℕ) • (((2 : ℕ) • (((2 : ℕ) • (P))))))))) + (-(rotation L (((2 : ℕ) • (P))))) = -((9 : ℕ) • P) - (2 : ℕ) • rotation L P
  simp only [map_add, map_nsmul, map_neg]
  abel

end
end ManuscriptAudit.Paper5OrdinarySixtySevenFrobenius

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper5OrdinarySixtySevenFrobenius.native_eq_rotation
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
