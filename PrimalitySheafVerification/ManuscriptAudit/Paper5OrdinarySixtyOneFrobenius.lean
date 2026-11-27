import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.CubicExecutableCoordinateChain
import PrimalitySheafVerification.ManuscriptAudit.CubicCoordinateChainFrobenius

/-! The exact native prime-field Frobenius for the printed p=61 cubic. -/

namespace ManuscriptAudit.Paper5OrdinarySixtyOneFrobenius

open Polynomial WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate CubicThreeTorsionCard
open CubicCoordinateChain CubicCoordinateChainFrobenius CubicExecutableCoordinateChain CubicExecutableFractions
open CubicFrobeniusScaling

noncomputable section

local instance : Fact (Nat.Prime 61) := ⟨by decide⟩

private abbrev CF := CoefficientFraction (ZMod 61)

private def m2 : CF := ⟨[0, -29], [1, 1]⟩
private def u2 : CF := ⟨[-2, -15], [1, 1]⟩
private def v2 : CF := ⟨[-1, -28, 23], [1, 2, 1]⟩
private def m4 : CF := ⟨[0, -13, -12, 16], [-8, 12, 21, 1]⟩
private def u4 : CF := ⟨[12, 16, -5, 1, 27, -19], [3, -12, 3, -3, -20, 1]⟩
private def v4 : CF := ⟨[-24, -14, -25, 9, -28, 21, -2, 4, -20], [-24, 10, 17, -6, -8, -3, 16, 1, 1]⟩
private def m5 : CF := ⟨[0, -18, -27, 18, 11, 0, 17, -2], [7, 18, -5, -13, 3, -26, -25, 1]⟩
private def u5 : CF := ⟨[20, -4, 27, 8, -6, 5, 12, -10, 22], [-4, 11, 4, 26, 7, -6, 7, 30, 1]⟩
private def v5 : CF := ⟨[27, 10, 16, -7, 30, 25, 17, -11, 15, -22, 26,
    -22, -20], [-27, -3, -7, -15, -23, -11, -3, -2, 7, -14, -18,
    -16, 1]⟩
private def mF : CF := ⟨[0, 4, 16, -8, 3, -18, 17, 17, -13, 0, 3,
    6, -2, -11, 28, -25, -5, -1], [7, 18, -5, -13, 3, -26, -25, 1]⟩

private def targetX : CF := CoefficientFraction.polynomial (CubicCoefficientArithmetic.pow [0, 1] 20)
private def targetY : CF := CoefficientFraction.polynomial (CubicCoefficientArithmetic.pow [1, 1] 30)

set_option maxRecDepth 60000
set_option maxHeartbeats 4500000

private def step2 : Program 1 47 (.double .identity) u2 v2 :=
  .double (m := m2) .identity (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private def step4 : Program 1 47 (.double (.double .identity)) u4 v4 :=
  .double (m := m4) step2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private def step5 : Program 1 47 (.add .identity (.double (.double .identity))) u5 v5 :=
  .add (m := m5) .identity step4 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private def term : Term := .add (.add .identity (.double (.double .identity))) (.neg (.rotate (.double (.double .identity))))

private def checked : Program 1 47 term targetX targetY :=
  .add (m := mF) step5 (.neg (.rotate step4)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private theorem targetX_eq : targetX.toFraction =
    CubicFractionCertificates.Fraction.polynomial (X ^ 20) := by
  simp [targetX, CubicCoefficientArithmetic.expand]

private theorem targetY_eq : targetY.toFraction =
    CubicFractionCertificates.Fraction.polynomial ((X + C (1 : ZMod 61)) ^ 30) := by
  simp [targetY, CubicCoefficientArithmetic.expand, add_comm]

variable (L : Type*) [Field L] [Algebra (ZMod 61) L] [IsAlgClosed L] [DecidableEq L]

abbrev a : L := algebraMap (ZMod 61) L (1 : ZMod 61)
abbrev Points := (Curve (a L)).Point

theorem two_ne_zero : (2 : L) ≠ 0 := by
  simpa only [map_ofNat] using
    (map_ne_zero (algebraMap (ZMod 61) L)).mpr (by decide : (2 : ZMod 61) ≠ 0)

theorem three_ne_zero : (3 : L) ≠ 0 := by
  simpa only [map_ofNat] using
    (map_ne_zero (algebraMap (ZMod 61) L)).mpr (by decide : (3 : ZMod 61) ≠ 0)

theorem cube_rotation : (algebraMap (ZMod 61) L (47 : ZMod 61)) ^ 3 = 1 := by
  simpa only [map_pow, map_one] using congrArg (algebraMap (ZMod 61) L)
    (by decide : (47 : ZMod 61) ^ 3 = 1)

theorem rotation_ne_one : algebraMap (ZMod 61) L (47 : ZMod 61) ≠ 1 := by
  intro h
  exact (by decide : (47 : ZMod 61) ≠ 1)
    ((algebraMap (ZMod 61) L).injective (h.trans (map_one (algebraMap (ZMod 61) L)).symm))

theorem discriminant_ne_zero : (shortCubic (0 : L) (a L)).Δ ≠ 0 :=
  shortCubic_discriminant_ne_zero (two_ne_zero L) (three_ne_zero L) (by simp [a])

def rotation : AddMonoid.End (Points L) :=
  CubicCubeRotation.rotate (algebraMap (ZMod 61) L (47 : ZMod 61))
    (cube_rotation L) (discriminant_ne_zero L)

def nativeFrobenius : AddMonoid.End (Points L) :=
  nativeMap (ZMod 61) L (FiniteField.frobeniusAlgHom (ZMod 61) L) 1

theorem native_eq_rotation : nativeFrobenius L = ((5 : ℕ) • (1 : AddMonoid.End (Points L))) - (4 : ℕ) • rotation L := by
  have h := compiles checked
  rw [targetX_eq, targetY_eq] at h
  obtain ⟨chain, hGuard⟩ := h
  have hEq := native_eq_of_chain (p := 61) (L := L)
    (by decide : 61 = 3 * 20 + 1) (by decide : 61 = 2 * 30 + 1)
    (two_ne_zero L) (cube_rotation L) (discriminant_ne_zero L) chain hGuard
  change nativeFrobenius L = term.hom (rotation L) at hEq
  refine hEq.trans ?_
  apply AddMonoidHom.ext
  intro P
  change (P + ((2 : ℕ) • (((2 : ℕ) • (P))))) + (-(rotation L (((2 : ℕ) • (((2 : ℕ) • (P))))))) = ((5 : ℕ) • P) - (4 : ℕ) • rotation L P
  simp only [map_add, map_nsmul, map_neg]
  abel

end
end ManuscriptAudit.Paper5OrdinarySixtyOneFrobenius

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper5OrdinarySixtyOneFrobenius.native_eq_rotation
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
