import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.CubicExecutableCoordinateChain
import PrimalitySheafVerification.ManuscriptAudit.CubicCoordinateChainFrobenius

/-! The exact native prime-field Frobenius for the printed p=79 cubic. -/

namespace ManuscriptAudit.Paper5OrdinarySeventyNineFrobenius

open Polynomial WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate CubicThreeTorsionCard
open CubicCoordinateChain CubicCoordinateChainFrobenius CubicExecutableCoordinateChain CubicExecutableFractions
open CubicFrobeniusScaling

noncomputable section

local instance : Fact (Nat.Prime 79) := ⟨by decide⟩

private abbrev CF := CoefficientFraction (ZMod 79)

private def m2 : CF := ⟨[0, -38], [1, 1]⟩
private def u2 : CF := ⟨[-2, 20], [1, 1]⟩
private def v2 : CF := ⟨[-1, -37, 10], [1, 2, 1]⟩
private def m3 : CF := ⟨[29, -27, -12], [4, 5, 1]⟩
private def u3 : CF := ⟨[-28, -21, -37, -35], [0, 16, 8, 1]⟩
private def v3 : CF := ⟨[22, -6, 22, 14, -38], [0, -15, -31, 12, 1]⟩
private def m4 : CF := ⟨[0, -31, -12, -19], [-8, 12, 21, 1]⟩
private def u4 : CF := ⟨[19, -35, -9, 26, -34, 5], [-15, -19, -15, 29, -38, 1]⟩
private def v4 : CF := ⟨[-38, 39, 30, 30, 13, 18, 31, 39, 21], [-38, -28, -28, -36, 2, -28, 33, -17, 1]⟩
private def m5 : CF := ⟨[0, 19, -11, -3, 36, -16, -6, 5], [-17, 18, 35, 8, -29, -20, 18, 1]⟩
private def u5 : CF := ⟨[-9, -30, 3, -30, -7, 35, 22, -20, 19], [-14, -17, -30, -4, -18, -36, -8, -6, 1]⟩
private def v5 : CF := ⟨[10, -8, 0, 26, -31, -1, 20, -22, -25, -18, 9,
    23, -12], [-10, 10, -15, -18, 13, -16, 25, 0, 36, 35, -38,
    -9, 1]⟩
private def m10 : CF := ⟨[0, -20, -28, -7, 34, 5, 29, 27, -18, 24, -31,
    -32, -6, -30, 3, -36, 16, 24], [-10, -25, -4, -5, 34, -39, -3, 2, 16, 7, 35,
    25, -30, -13, 29, -15, 29, 1]⟩
private def u10 : CF := ⟨[-27, 26, -14, 22, -28, -1, 30, 27, 31, 13, 24,
    8, 0, -27, -12, -14, 30, 7, 13, 25, 6, -38,
    -21, 38, -38, -5, -32, -13, -25, 38, -10, 28, -6,
    -15], [21, 5, -11, -5, -14, 3, 22, -19, -16, -7, -32,
    -10, 30, 1, -16, 0, 23, 7, 30, 8, 37, -5,
    -9, 5, -5, -36, -4, 11, 4, -29, 14, -36, -22,
    1]⟩
private def v10 : CF := ⟨[27, -5, -29, 26, -1, 3, -12, -37, 25, 31, 39,
    -18, 31, -23, -19, -12, 13, -15, -25, -12, 27, -8,
    -14, 26, -4, 39, -39, 20, -36, 33, 1, -26, 13,
    4, 17, 24, 19, 24, 23, -2, -26, 37, -23, -14,
    20, -15, 1, 7, -3, 33, 38], [27, -22, -20, -37, -29, -17, 23, -16, -2, -39, 15,
    10, -30, 31, -29, 2, 28, 21, -13, -27, -27, 19,
    4, 34, 35, 16, 8, -30, -9, 24, -34, 2, 36,
    27, 25, -38, 0, -18, 19, -23, -26, -31, -11, 34,
    -12, -18, 29, -39, 22, 7, 1]⟩
private def mF : CF := ⟨[-26, 26, 10, -16, 2, 19, 18, -6, 33, 31, 5,
    34, -3, -22, -6, -19, -15, 22, -30, 31, -8, 28,
    -11, 31, 0, 24, -12, -5, 25, 4, 7, -1], [39, -31, 38, -24, -27, 36, 28, 5, -13, -35, -11,
    -23, -16, -3, 24, -31, 22, 33, 1]⟩

private def targetX : CF := CoefficientFraction.polynomial (CubicCoefficientArithmetic.pow [0, 1] 26)
private def targetY : CF := CoefficientFraction.polynomial (CubicCoefficientArithmetic.pow [1, 1] 39)

set_option maxRecDepth 60000
set_option maxHeartbeats 4500000

private def step2 : Program 1 55 (.double .identity) u2 v2 :=
  .double (m := m2) .identity (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private def step3 : Program 1 55 (.add .identity (.double .identity)) u3 v3 :=
  .add (m := m3) .identity step2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private def step4 : Program 1 55 (.double (.double .identity)) u4 v4 :=
  .double (m := m4) step2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private def step5 : Program 1 55 (.add .identity (.double (.double .identity))) u5 v5 :=
  .add (m := m5) .identity step4 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private def step10 : Program 1 55 (.double (.add .identity (.double (.double .identity)))) u10 v10 :=
  .double (m := m10) step5 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private def term : Term := .add (.add .identity (.double .identity)) (.rotate (.double (.add .identity (.double (.double .identity)))))

private def checked : Program 1 55 term targetX targetY :=
  .add (m := mF) step3 (.rotate step10) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private theorem targetX_eq : targetX.toFraction =
    CubicFractionCertificates.Fraction.polynomial (X ^ 26) := by
  simp [targetX, CubicCoefficientArithmetic.expand]

private theorem targetY_eq : targetY.toFraction =
    CubicFractionCertificates.Fraction.polynomial ((X + C (1 : ZMod 79)) ^ 39) := by
  simp [targetY, CubicCoefficientArithmetic.expand, add_comm]

variable (L : Type*) [Field L] [Algebra (ZMod 79) L] [IsAlgClosed L] [DecidableEq L]

abbrev a : L := algebraMap (ZMod 79) L (1 : ZMod 79)
abbrev Points := (Curve (a L)).Point

theorem two_ne_zero : (2 : L) ≠ 0 := by
  simpa only [map_ofNat] using
    (map_ne_zero (algebraMap (ZMod 79) L)).mpr (by decide : (2 : ZMod 79) ≠ 0)

theorem three_ne_zero : (3 : L) ≠ 0 := by
  simpa only [map_ofNat] using
    (map_ne_zero (algebraMap (ZMod 79) L)).mpr (by decide : (3 : ZMod 79) ≠ 0)

theorem cube_rotation : (algebraMap (ZMod 79) L (55 : ZMod 79)) ^ 3 = 1 := by
  simpa only [map_pow, map_one] using congrArg (algebraMap (ZMod 79) L)
    (by decide : (55 : ZMod 79) ^ 3 = 1)

theorem rotation_ne_one : algebraMap (ZMod 79) L (55 : ZMod 79) ≠ 1 := by
  intro h
  exact (by decide : (55 : ZMod 79) ≠ 1)
    ((algebraMap (ZMod 79) L).injective (h.trans (map_one (algebraMap (ZMod 79) L)).symm))

theorem discriminant_ne_zero : (shortCubic (0 : L) (a L)).Δ ≠ 0 :=
  shortCubic_discriminant_ne_zero (two_ne_zero L) (three_ne_zero L) (by simp [a])

def rotation : AddMonoid.End (Points L) :=
  CubicCubeRotation.rotate (algebraMap (ZMod 79) L (55 : ZMod 79))
    (cube_rotation L) (discriminant_ne_zero L)

def nativeFrobenius : AddMonoid.End (Points L) :=
  nativeMap (ZMod 79) L (FiniteField.frobeniusAlgHom (ZMod 79) L) 1

theorem native_eq_rotation : nativeFrobenius L = ((3 : ℕ) • (1 : AddMonoid.End (Points L))) + (10 : ℕ) • rotation L := by
  have h := compiles checked
  rw [targetX_eq, targetY_eq] at h
  obtain ⟨chain, hGuard⟩ := h
  have hEq := native_eq_of_chain (p := 79) (L := L)
    (by decide : 79 = 3 * 26 + 1) (by decide : 79 = 2 * 39 + 1)
    (two_ne_zero L) (cube_rotation L) (discriminant_ne_zero L) chain hGuard
  change nativeFrobenius L = term.hom (rotation L) at hEq
  refine hEq.trans ?_
  apply AddMonoidHom.ext
  intro P
  change (P + ((2 : ℕ) • (P))) + rotation L (((2 : ℕ) • ((P + ((2 : ℕ) • (((2 : ℕ) • (P)))))))) = ((3 : ℕ) • P) + (10 : ℕ) • rotation L P
  simp only [map_add, map_nsmul, map_neg]
  abel

end
end ManuscriptAudit.Paper5OrdinarySeventyNineFrobenius

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper5OrdinarySeventyNineFrobenius.native_eq_rotation
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
