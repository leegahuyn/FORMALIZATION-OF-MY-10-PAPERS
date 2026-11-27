import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.CubicExecutableCoordinateChain
import PrimalitySheafVerification.ManuscriptAudit.CubicCoordinateChainFrobenius

/-! The exact native prime-field Frobenius for the printed p=97 cubic. -/

namespace ManuscriptAudit.Paper5OrdinaryNinetySevenFrobenius

open Polynomial WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate CubicThreeTorsionCard
open CubicCoordinateChain CubicCoordinateChainFrobenius CubicExecutableCoordinateChain CubicExecutableFractions
open CubicFrobeniusScaling

noncomputable section

local instance : Fact (Nat.Prime 97) := ⟨by decide⟩

private abbrev CF := CoefficientFraction (ZMod 97)

private def m2 : CF := ⟨[0, -47], [1, 1]⟩
private def u2 : CF := ⟨[-2, -24], [1, 1]⟩
private def v2 : CF := ⟨[-1, -46, -12], [1, 2, 1]⟩
private def m3 : CF := ⟨[35, -33, -15], [4, 5, 1]⟩
private def u3 : CF := ⟨[-36, -27, -43, -43], [0, 16, 8, 1]⟩
private def v3 : CF := ⟨[-1, -37, 42, -17, 18], [0, -33, 48, 12, 1]⟩
private def m4 : CF := ⟨[0, 48, -12, 25], [-8, 12, 21, 1]⟩
private def u4 : CF := ⟨[-35, 22, -38, -10, -34, -6], [-33, 35, -33, 36, 41, 1]⟩
private def v4 : CF := ⟨[-27, -23, -6, -12, 27, 4, -44, -5, 47], [-27, 3, -9, 18, 28, 43, 36, -35, 1]⟩
private def m8 : CF := ⟨[0, 36, -12, -40, 2, 11, 25, 5, 28, -15, -20,
    -36], [-47, -36, 45, 33, 16, 42, 10, 25, 31, -18, -8,
    1]⟩
private def u8 : CF := ⟨[-18, -25, 3, 36, 26, 20, 7, 44, -4, 38, 29,
    -27, -33, -5, -40, -27, -29, 3, 44, 10, 36, 47], [-22, 11, -35, -2, -10, 14, 6, 14, -24, -45, -16,
    42, 6, 47, -19, -13, -2, -39, 14, 45, -17, 1]⟩
private def v8 : CF := ⟨[33, 39, -8, 43, 26, -22, -38, -46, -14, 13, -18,
    34, -25, -9, -43, -36, -17, -2, -42, 14, 27, 30,
    -14, 27, -35, -18, 18, -14, 26, -13, -34, -4, 18], [-33, -16, -32, -41, 45, 37, 29, 6, -33, -39, 17,
    4, 27, 34, -3, 46, 27, -31, 35, 10, -6, 20,
    6, 18, 23, -16, 2, -29, -8, -9, -31, -25, 1]⟩
private def mF : CF := ⟨[-4, 13, 2, 1, 34, 31, -14, 42, 7, -24, -24,
    28, 43, 12, -22, -30, -11, 6, 30, -6, 2, 47,
    -28, -31, 44, 36, -13, -44, -1], [6, 3, 47, -17, 0, -10, -15, 13, -45, -41, 47,
    -4, 1]⟩

private def targetX : CF := CoefficientFraction.polynomial (CubicCoefficientArithmetic.pow [0, 1] 32)
private def targetY : CF := CoefficientFraction.polynomial (CubicCoefficientArithmetic.pow [1, 1] 48)

set_option maxRecDepth 60000
set_option maxHeartbeats 4500000

private def step2 : Program 1 61 (.double .identity) u2 v2 :=
  .double (m := m2) .identity (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private def step3 : Program 1 61 (.add .identity (.double .identity)) u3 v3 :=
  .add (m := m3) .identity step2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private def step4 : Program 1 61 (.double (.double .identity)) u4 v4 :=
  .double (m := m4) step2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private def step8 : Program 1 61 (.double (.double (.double .identity))) u8 v8 :=
  .double (m := m8) step4 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private def term : Term := .add (.add .identity (.double .identity)) (.neg (.rotate (.double (.double (.double .identity)))))

private def checked : Program 1 61 term targetX targetY :=
  .add (m := mF) step3 (.neg (.rotate step8)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private theorem targetX_eq : targetX.toFraction =
    CubicFractionCertificates.Fraction.polynomial (X ^ 32) := by
  simp [targetX, CubicCoefficientArithmetic.expand]

private theorem targetY_eq : targetY.toFraction =
    CubicFractionCertificates.Fraction.polynomial ((X + C (1 : ZMod 97)) ^ 48) := by
  simp [targetY, CubicCoefficientArithmetic.expand, add_comm]

variable (L : Type*) [Field L] [Algebra (ZMod 97) L] [IsAlgClosed L] [DecidableEq L]

abbrev a : L := algebraMap (ZMod 97) L (1 : ZMod 97)
abbrev Points := (Curve (a L)).Point

theorem two_ne_zero : (2 : L) ≠ 0 := by
  simpa only [map_ofNat] using
    (map_ne_zero (algebraMap (ZMod 97) L)).mpr (by decide : (2 : ZMod 97) ≠ 0)

theorem three_ne_zero : (3 : L) ≠ 0 := by
  simpa only [map_ofNat] using
    (map_ne_zero (algebraMap (ZMod 97) L)).mpr (by decide : (3 : ZMod 97) ≠ 0)

theorem cube_rotation : (algebraMap (ZMod 97) L (61 : ZMod 97)) ^ 3 = 1 := by
  simpa only [map_pow, map_one] using congrArg (algebraMap (ZMod 97) L)
    (by decide : (61 : ZMod 97) ^ 3 = 1)

theorem rotation_ne_one : algebraMap (ZMod 97) L (61 : ZMod 97) ≠ 1 := by
  intro h
  exact (by decide : (61 : ZMod 97) ≠ 1)
    ((algebraMap (ZMod 97) L).injective (h.trans (map_one (algebraMap (ZMod 97) L)).symm))

theorem discriminant_ne_zero : (shortCubic (0 : L) (a L)).Δ ≠ 0 :=
  shortCubic_discriminant_ne_zero (two_ne_zero L) (three_ne_zero L) (by simp [a])

def rotation : AddMonoid.End (Points L) :=
  CubicCubeRotation.rotate (algebraMap (ZMod 97) L (61 : ZMod 97))
    (cube_rotation L) (discriminant_ne_zero L)

def nativeFrobenius : AddMonoid.End (Points L) :=
  nativeMap (ZMod 97) L (FiniteField.frobeniusAlgHom (ZMod 97) L) 1

theorem native_eq_rotation : nativeFrobenius L = ((3 : ℕ) • (1 : AddMonoid.End (Points L))) - (8 : ℕ) • rotation L := by
  have h := compiles checked
  rw [targetX_eq, targetY_eq] at h
  obtain ⟨chain, hGuard⟩ := h
  have hEq := native_eq_of_chain (p := 97) (L := L)
    (by decide : 97 = 3 * 32 + 1) (by decide : 97 = 2 * 48 + 1)
    (two_ne_zero L) (cube_rotation L) (discriminant_ne_zero L) chain hGuard
  change nativeFrobenius L = term.hom (rotation L) at hEq
  refine hEq.trans ?_
  apply AddMonoidHom.ext
  intro P
  change (P + ((2 : ℕ) • (P))) + (-(rotation L (((2 : ℕ) • (((2 : ℕ) • (((2 : ℕ) • (P))))))))) = ((3 : ℕ) • P) - (8 : ℕ) • rotation L P
  simp only [map_add, map_nsmul, map_neg]
  abel

end
end ManuscriptAudit.Paper5OrdinaryNinetySevenFrobenius

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper5OrdinaryNinetySevenFrobenius.native_eq_rotation
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
