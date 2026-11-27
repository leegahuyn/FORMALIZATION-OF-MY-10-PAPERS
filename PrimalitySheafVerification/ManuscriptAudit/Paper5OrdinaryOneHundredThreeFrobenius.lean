import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.CubicExecutableCoordinateChain
import PrimalitySheafVerification.ManuscriptAudit.CubicCoordinateChainFrobenius

/-! The exact native prime-field Frobenius for the printed p=103 cubic. -/

namespace ManuscriptAudit.Paper5OrdinaryOneHundredThreeFrobenius

open Polynomial WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate CubicThreeTorsionCard
open CubicCoordinateChain CubicCoordinateChainFrobenius CubicExecutableCoordinateChain CubicExecutableFractions
open CubicFrobeniusScaling

noncomputable section

local instance : Fact (Nat.Prime 103) := ⟨by decide⟩

private abbrev CF := CoefficientFraction (ZMod 103)

private def m2 : CF := ⟨[0, -50], [1, 1]⟩
private def u2 : CF := ⟨[-2, 26], [1, 1]⟩
private def v2 : CF := ⟨[-1, -49, 13], [1, 2, 1]⟩
private def m4 : CF := ⟨[0, 48, -12, -25], [-8, 12, 21, 1]⟩
private def u4 : CF := ⟨[50, -38, 29, -22, -34, -45], [-39, -50, -39, 12, 41, 1]⟩
private def v4 : CF := ⟨[3, -25, 24, -32, 41, -51, 10, 45, -37], [3, 35, 26, -5, -23, -24, -42, -41, 1]⟩
private def m8 : CF := ⟨[0, 10, 26, -23, 31, 29, -7, -31, -30, -13, 4,
    39], [9, -37, 45, -34, 23, -43, 13, -13, 26, -50, 17,
    1]⟩
private def u8 : CF := ⟨[-30, 46, 45, -34, -12, 5, -39, -17, 33, 50, -48,
    26, 5, 36, -14, -2, 33, -39, 4, -12, -31, -37], [-22, -26, 42, 33, -22, 48, 2, -40, 16, 29, -34,
    -23, 49, -15, 3, 4, -41, 12, 50, -50, 33, 1]⟩
private def v8 : CF := ⟨[-8, 30, 0, 47, -19, -32, 50, -5, 26, 23, -49,
    21, 35, -10, 25, 18, 29, -31, 22, 43, 46, 36,
    42, -6, -46, -5, 38, -26, -49, 31, -16, 12, 34], [8, -38, 41, -31, 25, 3, -12, 36, 14, -48, -14,
    10, -32, 42, -9, -12, 9, 9, 45, -36, 39, 11,
    -6, -26, -24, 46, 13, -36, -16, 48, 49, 50, 1]⟩
private def m9 : CF := ⟨[-27, -10, 9, 14, 9, 7, -11, -27, -28, 40, 6,
    10, 44, 25, -7, -41, -22, 21, -13, -1, 1, 18,
    -20, -34, -9], [33, -37, -8, -5, 46, 51, -9, -6, -49, 14, -15,
    6, 13, -51, 0, 33, -3, 30, 47, 43, 0, -25,
    -25, -22, 1]⟩
private def u9 : CF := ⟨[9, 35, 30, 7, -40, 8, 34, 34, -42, -47, -26,
    5, -34, -36, 0, -31, 20, 26, 1, -1, -30, 48,
    -28, 9, -14, 42, 18, 14], [0, 2, 13, -23, -11, 40, -45, 6, 22, -9, -20,
    37, 15, -49, -15, 3, -17, -43, -47, 7, -20, 47,
    48, 31, 3, 13, 25, 1]⟩
private def v9 : CF := ⟨[27, 41, 27, -8, 43, 6, -49, 7, -25, -29, -30,
    -26, -49, -35, 42, 25, 18, -36, 46, -11, 1, 49,
    -38, -13, -42, 19, -19, 34, -48, -22, -23, -35, 16,
    17, -29, 32, 15, -38, -7, -51, 13], [0, -27, 20, 9, -9, 49, 20, 35, -3, -7, -30,
    -34, 27, -29, -32, 15, -50, 48, -50, -47, -6, -5,
    17, 49, -2, 19, -7, -43, -45, -21, 44, 43, -16,
    -10, -48, -35, 11, 12, 35, -14, 1]⟩
private def mF : CF := ⟨[3, -30, -51, -27, -8, -12, -38, 31, 40, -15, 11,
    40, -14, -39, -50, -1, 0, 50, -32, 49, 20, -25,
    -8, 20, 2, -15, 33, -24, 16, 14, -13, -1], [38, 7, -6, -32, 4, -38, -1, 34, 50, -28, -37,
    -31, 31, -38, 1]⟩

private def targetX : CF := CoefficientFraction.polynomial (CubicCoefficientArithmetic.pow [0, 1] 34)
private def targetY : CF := CoefficientFraction.polynomial (CubicCoefficientArithmetic.pow [1, 1] 51)

set_option maxRecDepth 60000
set_option maxHeartbeats 4500000

private def step2 : Program 1 56 (.double .identity) u2 v2 :=
  .double (m := m2) .identity (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private def step4 : Program 1 56 (.double (.double .identity)) u4 v4 :=
  .double (m := m4) step2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private def step8 : Program 1 56 (.double (.double (.double .identity))) u8 v8 :=
  .double (m := m8) step4 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private def step9 : Program 1 56 (.add .identity (.double (.double (.double .identity)))) u9 v9 :=
  .add (m := m9) .identity step8 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private def term : Term := .add (.add .identity (.double (.double (.double .identity)))) (.neg (.rotate (.double .identity)))

private def checked : Program 1 56 term targetX targetY :=
  .add (m := mF) step9 (.neg (.rotate step2)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private theorem targetX_eq : targetX.toFraction =
    CubicFractionCertificates.Fraction.polynomial (X ^ 34) := by
  simp [targetX, CubicCoefficientArithmetic.expand]

private theorem targetY_eq : targetY.toFraction =
    CubicFractionCertificates.Fraction.polynomial ((X + C (1 : ZMod 103)) ^ 51) := by
  simp [targetY, CubicCoefficientArithmetic.expand, add_comm]

variable (L : Type*) [Field L] [Algebra (ZMod 103) L] [IsAlgClosed L] [DecidableEq L]

abbrev a : L := algebraMap (ZMod 103) L (1 : ZMod 103)
abbrev Points := (Curve (a L)).Point

theorem two_ne_zero : (2 : L) ≠ 0 := by
  simpa only [map_ofNat] using
    (map_ne_zero (algebraMap (ZMod 103) L)).mpr (by decide : (2 : ZMod 103) ≠ 0)

theorem three_ne_zero : (3 : L) ≠ 0 := by
  simpa only [map_ofNat] using
    (map_ne_zero (algebraMap (ZMod 103) L)).mpr (by decide : (3 : ZMod 103) ≠ 0)

theorem cube_rotation : (algebraMap (ZMod 103) L (56 : ZMod 103)) ^ 3 = 1 := by
  simpa only [map_pow, map_one] using congrArg (algebraMap (ZMod 103) L)
    (by decide : (56 : ZMod 103) ^ 3 = 1)

theorem rotation_ne_one : algebraMap (ZMod 103) L (56 : ZMod 103) ≠ 1 := by
  intro h
  exact (by decide : (56 : ZMod 103) ≠ 1)
    ((algebraMap (ZMod 103) L).injective (h.trans (map_one (algebraMap (ZMod 103) L)).symm))

theorem discriminant_ne_zero : (shortCubic (0 : L) (a L)).Δ ≠ 0 :=
  shortCubic_discriminant_ne_zero (two_ne_zero L) (three_ne_zero L) (by simp [a])

def rotation : AddMonoid.End (Points L) :=
  CubicCubeRotation.rotate (algebraMap (ZMod 103) L (56 : ZMod 103))
    (cube_rotation L) (discriminant_ne_zero L)

def nativeFrobenius : AddMonoid.End (Points L) :=
  nativeMap (ZMod 103) L (FiniteField.frobeniusAlgHom (ZMod 103) L) 1

theorem native_eq_rotation : nativeFrobenius L = ((9 : ℕ) • (1 : AddMonoid.End (Points L))) - (2 : ℕ) • rotation L := by
  have h := compiles checked
  rw [targetX_eq, targetY_eq] at h
  obtain ⟨chain, hGuard⟩ := h
  have hEq := native_eq_of_chain (p := 103) (L := L)
    (by decide : 103 = 3 * 34 + 1) (by decide : 103 = 2 * 51 + 1)
    (two_ne_zero L) (cube_rotation L) (discriminant_ne_zero L) chain hGuard
  change nativeFrobenius L = term.hom (rotation L) at hEq
  refine hEq.trans ?_
  apply AddMonoidHom.ext
  intro P
  change (P + ((2 : ℕ) • (((2 : ℕ) • (((2 : ℕ) • (P))))))) + (-(rotation L (((2 : ℕ) • (P))))) = ((9 : ℕ) • P) - (2 : ℕ) • rotation L P
  simp only [map_add, map_nsmul, map_neg]
  abel

end
end ManuscriptAudit.Paper5OrdinaryOneHundredThreeFrobenius

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper5OrdinaryOneHundredThreeFrobenius.native_eq_rotation
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
