import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.CubicExecutableCoordinateChain
import PrimalitySheafVerification.ManuscriptAudit.CubicCoordinateChainFrobenius

/-! The exact native prime-field Frobenius for the printed p=109 cubic. -/

namespace ManuscriptAudit.Paper5OrdinaryOneHundredNineFrobenius

open Polynomial WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate CubicThreeTorsionCard
open CubicCoordinateChain CubicCoordinateChainFrobenius CubicExecutableCoordinateChain CubicExecutableFractions
open CubicFrobeniusScaling

noncomputable section

local instance : Fact (Nat.Prime 109) := ⟨by decide⟩

private abbrev CF := CoefficientFraction (ZMod 109)

private def m2 : CF := ⟨[0, -53], [1, 1]⟩
private def u2 : CF := ⟨[-2, -27], [1, 1]⟩
private def v2 : CF := ⟨[-1, -52, 41], [1, 2, 1]⟩
private def m4 : CF := ⟨[0, 48, -12, 28], [-8, 12, 21, 1]⟩
private def u4 : CF := ⟨[38, 11, -1, -34, -34, -34], [-45, -38, -45, -12, 41, 1]⟩
private def v4 : CF := ⟨[33, -14, -53, 35, 7, -9, -45, -8, 46], [33, -18, 49, 21, -38, -31, -11, -47, 1]⟩
private def m5 : CF := ⟨[0, 28, 42, 33, 7, 16, -24, -48], [39, 49, 25, -20, 12, 34, -12, 1]⟩
private def u5 : CF := ⟨[-49, 23, 4, 1, 35, 32, 29, 4, 48], [-12, -41, -28, 4, -48, 21, 12, 43, 1]⟩
private def v5 : CF := ⟨[-4, -41, -45, -35, -40, -4, 20, -27, -46, 18, -21,
    48, -34], [4, -34, 44, 23, 4, 21, -2, 32, 1, -34, -38,
    10, 1]⟩
private def m3 : CF := ⟨[39, -37, -17], [4, 5, 1]⟩
private def u3 : CF := ⟨[-5, -31, -47, -12], [0, 16, 8, 1]⟩
private def v3 : CF := ⟨[-23, -28, 19, -8, -4], [0, -45, 48, 12, 1]⟩
private def m6 : CF := ⟨[-23, 20, 22, 34, -31, 13, -54], [23, -25, 49, -36, -18, 7, 1]⟩
private def u6 : CF := ⟨[-26, 31, -15, 16, 23, 3, -45, 44, -28, 27, -20,
    9, -3], [0, -16, -44, -20, -53, 47, 45, -54, 24, 3, 0,
    13, 1]⟩
private def v6 : CF := ⟨[54, 25, 9, -39, 2, 47, 37, -9, 21, -3, -37,
    -14, -50, 15, 13, -4, 53, -26, 54], [0, -41, 42, -35, -10, 28, -29, 27, 24, -39, 4,
    44, 24, 18, -47, -49, -36, 20, 1]⟩
private def m12 : CF := ⟨[43, 40, 9, 54, 46, 28, 46, -2, 53, -45, 17,
    -34, -54, -44, -20, 27, -22, -17, -13, -15, -1, 40,
    51, 53, -27], [23, 24, 13, -24, -52, 45, 17, 37, 32, 45, -48,
    -9, 41, 39, -13, 35, -2, 11, 30, -12, 6, 38,
    22, -50, 1]⟩
private def u12 : CF := ⟨[48, 31, 46, -1, -18, 42, 21, -48, -27, 37, -41,
    -35, 4, 47, -10, -51, -1, -21, 7, -16, 10, 52,
    15, -1, -53, 49, 19, 18, 5, -38, -50, -41, 24,
    -24, 47, -18, -38, 30, 13, 44, 48, 2, -53, -53,
    1, -2, -14, 33, -28], [0, -16, 30, 54, 11, -7, 47, 48, 32, -49, -7,
    35, 13, -41, -10, 2, -1, -30, -24, -53, 10, 52,
    -27, -24, 24, 5, -47, -38, 11, -23, -27, -26, -22,
    -30, 12, -13, 40, 41, -43, -51, -2, -4, 6, 19,
    48, 27, 29, 8, 1]⟩
private def v12 : CF := ⟨[34, -42, -50, -20, 33, -21, -10, -25, -7, -11, 33,
    -17, -46, -5, -47, -13, -15, 24, -54, -15, -9, 37,
    -12, 15, 9, 12, 21, -8, -17, -24, 18, -42, -37,
    -9, 52, -49, 34, 46, 13, 47, -3, 51, 17, 27,
    -14, 54, 40, -3, 8, -52, 5, 42, 7, 54, 46,
    -16, -17, 22, 12, -7, 17, 49, -40, 0, 25, -26,
    -29, -16, 45, -3, 31, 37, 34], [0, -41, -21, 10, 34, 45, -13, 38, -26, -14, -9,
    42, -50, 18, 29, -30, 46, 54, 24, 33, 3, -27,
    -28, 54, 17, 51, -8, -52, -16, -42, -34, 51, -8,
    47, -30, 28, 28, 7, -3, 40, -28, -33, 9, 24,
    7, 23, 47, 20, -8, -52, -40, -50, -9, 47, 35,
    -35, -39, -16, 51, -13, -47, -52, 32, 3, 10, 41,
    47, 5, -27, -10, -22, -42, 1]⟩
private def mF : CF := ⟨[-26, 6, -51, -51, -43, -41, -17, -54, -31, -28, 44,
    -29, 43, 17, -24, 50, -43, 29, -48, 29, -14, 16,
    6, -2, -46, 49, -19, 0, -30, -16, -48, -48, 37,
    -43, 42, -11, -47, -37, -47, 11, -2, 27, -13, -24,
    10, 29, -1], [-44, 44, -32, 41, -54, 41, -23, 2, 39, -12, -11,
    -24, -25, 46, 48, 6, -13, 42, -24, 5, -38, 26,
    -3, 26, -2, -25, -11, 26, 1]⟩

private def targetX : CF := CoefficientFraction.polynomial (CubicCoefficientArithmetic.pow [0, 1] 36)
private def targetY : CF := CoefficientFraction.polynomial (CubicCoefficientArithmetic.pow [1, 1] 54)

set_option maxRecDepth 60000
set_option maxHeartbeats 4500000

private def step2 : Program 1 45 (.double .identity) u2 v2 :=
  .double (m := m2) .identity (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private def step4 : Program 1 45 (.double (.double .identity)) u4 v4 :=
  .double (m := m4) step2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private def step5 : Program 1 45 (.add .identity (.double (.double .identity))) u5 v5 :=
  .add (m := m5) .identity step4 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private def step3 : Program 1 45 (.add .identity (.double .identity)) u3 v3 :=
  .add (m := m3) .identity step2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private def step6 : Program 1 45 (.double (.add .identity (.double .identity))) u6 v6 :=
  .double (m := m6) step3 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private def step12 : Program 1 45 (.double (.double (.add .identity (.double .identity)))) u12 v12 :=
  .double (m := m12) step6 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private def term : Term := .add (.neg (.add .identity (.double (.double .identity)))) (.neg (.rotate (.double (.double (.add .identity (.double .identity))))))

private def checked : Program 1 45 term targetX targetY :=
  .add (m := mF) (.neg step5) (.neg (.rotate step12)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private theorem targetX_eq : targetX.toFraction =
    CubicFractionCertificates.Fraction.polynomial (X ^ 36) := by
  simp [targetX, CubicCoefficientArithmetic.expand]

private theorem targetY_eq : targetY.toFraction =
    CubicFractionCertificates.Fraction.polynomial ((X + C (1 : ZMod 109)) ^ 54) := by
  simp [targetY, CubicCoefficientArithmetic.expand, add_comm]

variable (L : Type*) [Field L] [Algebra (ZMod 109) L] [IsAlgClosed L] [DecidableEq L]

abbrev a : L := algebraMap (ZMod 109) L (1 : ZMod 109)
abbrev Points := (Curve (a L)).Point

theorem two_ne_zero : (2 : L) ≠ 0 := by
  simpa only [map_ofNat] using
    (map_ne_zero (algebraMap (ZMod 109) L)).mpr (by decide : (2 : ZMod 109) ≠ 0)

theorem three_ne_zero : (3 : L) ≠ 0 := by
  simpa only [map_ofNat] using
    (map_ne_zero (algebraMap (ZMod 109) L)).mpr (by decide : (3 : ZMod 109) ≠ 0)

theorem cube_rotation : (algebraMap (ZMod 109) L (45 : ZMod 109)) ^ 3 = 1 := by
  simpa only [map_pow, map_one] using congrArg (algebraMap (ZMod 109) L)
    (by decide : (45 : ZMod 109) ^ 3 = 1)

theorem rotation_ne_one : algebraMap (ZMod 109) L (45 : ZMod 109) ≠ 1 := by
  intro h
  exact (by decide : (45 : ZMod 109) ≠ 1)
    ((algebraMap (ZMod 109) L).injective (h.trans (map_one (algebraMap (ZMod 109) L)).symm))

theorem discriminant_ne_zero : (shortCubic (0 : L) (a L)).Δ ≠ 0 :=
  shortCubic_discriminant_ne_zero (two_ne_zero L) (three_ne_zero L) (by simp [a])

def rotation : AddMonoid.End (Points L) :=
  CubicCubeRotation.rotate (algebraMap (ZMod 109) L (45 : ZMod 109))
    (cube_rotation L) (discriminant_ne_zero L)

def nativeFrobenius : AddMonoid.End (Points L) :=
  nativeMap (ZMod 109) L (FiniteField.frobeniusAlgHom (ZMod 109) L) 1

theorem native_eq_rotation : nativeFrobenius L = -((5 : ℕ) • (1 : AddMonoid.End (Points L))) - (12 : ℕ) • rotation L := by
  have h := compiles checked
  rw [targetX_eq, targetY_eq] at h
  obtain ⟨chain, hGuard⟩ := h
  have hEq := native_eq_of_chain (p := 109) (L := L)
    (by decide : 109 = 3 * 36 + 1) (by decide : 109 = 2 * 54 + 1)
    (two_ne_zero L) (cube_rotation L) (discriminant_ne_zero L) chain hGuard
  change nativeFrobenius L = term.hom (rotation L) at hEq
  refine hEq.trans ?_
  apply AddMonoidHom.ext
  intro P
  change (-((P + ((2 : ℕ) • (((2 : ℕ) • (P))))))) + (-(rotation L (((2 : ℕ) • (((2 : ℕ) • ((P + ((2 : ℕ) • (P)))))))))) = -((5 : ℕ) • P) - (12 : ℕ) • rotation L P
  simp only [map_add, map_nsmul, map_neg]
  abel

end
end ManuscriptAudit.Paper5OrdinaryOneHundredNineFrobenius

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper5OrdinaryOneHundredNineFrobenius.native_eq_rotation
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
