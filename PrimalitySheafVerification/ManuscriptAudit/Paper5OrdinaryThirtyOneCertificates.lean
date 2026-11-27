import Lean.Util.CollectAxioms
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import PrimalitySheafVerification.ManuscriptAudit.CubicExecutableFractions

/-! Exact polynomial certificates for the native characteristic-thirty-one addition chain. -/

namespace ManuscriptAudit.Paper5OrdinaryThirtyOneCertificates

open Polynomial CubicFractionCertificates CubicFractionCoordinateRules
open CubicExecutableFractions
open CoefficientFraction
open CubicCoefficientArithmetic (expand expand_ne_zero)

noncomputable section

local instance : Fact (Nat.Prime 31) := ⟨by decide⟩

private abbrev CFrac := CoefficientFraction (ZMod 31)

private def unitData : CFrac := CoefficientFraction.scalar 1
def unit : Fraction (ZMod 31) := Fraction.scalar 1

private def m2Data : CFrac := ⟨[0, -14], [1, 1]⟩
def m2 : Fraction (ZMod 31) := m2Data.toFraction

private def u2Data : CFrac := ⟨[-2, 8], [1, 1]⟩
def u2 : Fraction (ZMod 31) := u2Data.toFraction

private def v2Data : CFrac := ⟨[-1, -13, 4], [1, 2, 1]⟩
def v2 : Fraction (ZMod 31) := v2Data.toFraction

private def m3Data : CFrac := ⟨[13, -11, -4], [4, 5, 1]⟩
def m3 : Fraction (ZMod 31) := m3Data.toFraction

private def u3Data : CFrac := ⟨[14, -5, 10, 7], [0, -15, 8, 1]⟩
def u3 : Fraction (ZMod 31) := u3Data.toFraction

private def v3Data : CFrac := ⟨[4, -13, 10, 7, -8], [0, 2, -14, 12, 1]⟩
def v3 : Fraction (ZMod 31) := v3Data.toFraction

private def m6Data : CFrac := ⟨[2, 3, -1, 13, 6, -3, -15], [-2, 4, -9, -12, 10, 8, 1]⟩
def m6 : Fraction (ZMod 31) := m6Data.toFraction

private def u6Data : CFrac := ⟨[-3, -9, 10, 10, -8, 0, -5, 4, 8, 1, -11, 3, -6], [0, 4, 11, 10, -3, 10, 6, -13, 9, 5, 7, 15, 1]⟩
def u6 : Fraction (ZMod 31) := u6Data.toFraction

private def v6Data : CFrac := ⟨[-2, -9, -5, 11, -12, 12, 5, -13, 7, -3, 3, -15, -10, 10, 8, -13, -13, 8, -1], [0, -8, -6, -12, -8, 3, 15, 2, 3, 2, 1, -10, -11, -13, -8, 13, 13, -8, 1]⟩
def v6 : Fraction (ZMod 31) := v6Data.toFraction

private def mFData : CFrac := ⟨[-4, 9, -13, 2, 0, 0, -1, -7, -7, 13, 8, -1], [-2, 4, -9, -12, 10, 8, 1]⟩
def mF : Fraction (ZMod 31) := mFData.toFraction

private def rotatedSixData : CFrac := CoefficientFraction.scalar 5 * u6Data
def rotatedSixX : Fraction (ZMod 31) := Fraction.scalar 5 * u6

private def frobeniusXData : CFrac :=
  CoefficientFraction.polynomial (CubicCoefficientArithmetic.pow [0, 1] 10)
private def frobeniusYData : CFrac :=
  CoefficientFraction.polynomial (CubicCoefficientArithmetic.pow [1, 1] 15)

def frobeniusX : Fraction (ZMod 31) := Fraction.polynomial (X ^ 10)
def frobeniusY : Fraction (ZMod 31) := Fraction.polynomial ((X + 1) ^ 15)

private theorem fromFrobeniusX : frobeniusXData.toFraction = frobeniusX := by
  simp [frobeniusXData, frobeniusX, CubicCoefficientArithmetic.expand]

private theorem fromFrobeniusY : frobeniusYData.toFraction = frobeniusY := by
  simp [frobeniusYData, frobeniusY, CubicCoefficientArithmetic.expand, add_comm]

set_option maxRecDepth 40000
set_option maxHeartbeats 3000000

theorem slope_two : (tangentFraction 1 unit unit).CrossEq m2 := by
  simpa only [toFraction_tangent, unitData, toFraction_scalar, unit, m2, u2, v2, m3, u3, v3, m6, u6, v6, mF, rotatedSixX] using
    check_sound (show Check (tangent 1 unitData unitData) m2Data from by decide)

theorem x_two : (xFraction 1 unit unit m2).CrossEq u2 := by
  simpa only [toFraction_nextX, unitData, toFraction_scalar, unit, m2, u2, v2, m3, u3, v3, m6, u6, v6, mF, rotatedSixX] using
    check_sound (show Check (nextX 1 unitData unitData m2Data) u2Data from by decide)

theorem y_two : (yFraction unit unit u2 m2).CrossEq v2 := by
  simpa only [toFraction_nextY, unitData, toFraction_scalar, unit, m2, u2, v2, m3, u3, v3, m6, u6, v6, mF, rotatedSixX] using
    check_sound (show Check (nextY unitData unitData u2Data m2Data) v2Data from by decide)

theorem slope_three : (secantFraction unit unit u2 v2).CrossEq m3 := by
  simpa only [toFraction_secant, unitData, toFraction_scalar, unit, m2, u2, v2, m3, u3, v3, m6, u6, v6, mF, rotatedSixX] using
    check_sound (show Check (secant unitData unitData u2Data v2Data) m3Data from by decide)

theorem x_three : (xFraction 1 unit u2 m3).CrossEq u3 := by
  simpa only [toFraction_nextX, unitData, toFraction_scalar, unit, m2, u2, v2, m3, u3, v3, m6, u6, v6, mF, rotatedSixX] using
    check_sound (show Check (nextX 1 unitData u2Data m3Data) u3Data from by decide)

theorem y_three : (yFraction unit unit u3 m3).CrossEq v3 := by
  simpa only [toFraction_nextY, unitData, toFraction_scalar, unit, m2, u2, v2, m3, u3, v3, m6, u6, v6, mF, rotatedSixX] using
    check_sound (show Check (nextY unitData unitData u3Data m3Data) v3Data from by decide)

theorem slope_six : (tangentFraction 1 u3 v3).CrossEq m6 := by
  simpa only [toFraction_tangent, unitData, toFraction_scalar, unit, m2, u2, v2, m3, u3, v3, m6, u6, v6, mF, rotatedSixX] using
    check_sound (show Check (tangent 1 u3Data v3Data) m6Data from by decide)

theorem x_six : (xFraction 1 u3 u3 m6).CrossEq u6 := by
  simpa only [toFraction_nextX, unitData, toFraction_scalar, unit, m2, u2, v2, m3, u3, v3, m6, u6, v6, mF, rotatedSixX] using
    check_sound (show Check (nextX 1 u3Data u3Data m6Data) u6Data from by decide)

theorem y_six : (yFraction u3 v3 u6 m6).CrossEq v6 := by
  simpa only [toFraction_nextY, unitData, toFraction_scalar, unit, m2, u2, v2, m3, u3, v3, m6, u6, v6, mF, rotatedSixX] using
    check_sound (show Check (nextY u3Data v3Data u6Data m6Data) v6Data from by decide)

theorem slope_frobenius : (secantFraction unit unit rotatedSixX v6).CrossEq mF := by
  simpa only [toFraction_secant, unitData, toFraction_scalar, rotatedSixData, toFraction_mul, unit, m2, u2, v2, m3, u3, v3, m6, u6, v6, mF, rotatedSixX] using
    check_sound (show Check (secant unitData unitData rotatedSixData v6Data) mFData from by decide)

theorem x_frobenius : (xFraction 1 unit rotatedSixX mF).CrossEq frobeniusX := by
  simpa only [toFraction_nextX, unitData, toFraction_scalar, rotatedSixData, toFraction_mul, fromFrobeniusX, unit, m2, u2, v2, m3, u3, v3, m6, u6, v6, mF, rotatedSixX] using
    check_sound (show Check (nextX 1 unitData rotatedSixData mFData) frobeniusXData from by decide)

theorem y_frobenius : (yFraction unit unit frobeniusX mF).CrossEq frobeniusY := by
  simpa only [toFraction_nextY, unitData, toFraction_scalar, fromFrobeniusX, fromFrobeniusY, unit, m2, u2, v2, m3, u3, v3, m6, u6, v6, mF, rotatedSixX] using
    check_sound (show Check (nextY unitData unitData frobeniusXData mFData) frobeniusYData from by decide)

def excluded : List ((ZMod 31)[X]) :=
  [X, X + 1, m2.den, u2.den, v2.den, m3.den, u3.den, v3.den, m6.den, u6.den, v6.den, mF.den,
    v3.num, (unit - u2).num, (unit - rotatedSixX).num]

theorem excluded_nonzero : ∀ f ∈ excluded, f ≠ 0 := by
  intro f h
  simp only [excluded, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact X_ne_zero
  · have hMonic : ((X : (ZMod 31)[X]) ^ 1 + C 1).Monic := monic_X_pow_add_C 1 (by decide)
    simpa only [pow_one, map_one] using hMonic.ne_zero
  · exact expand_ne_zero (a := m2Data.den) (by decide)
  · exact expand_ne_zero (a := u2Data.den) (by decide)
  · exact expand_ne_zero (a := v2Data.den) (by decide)
  · exact expand_ne_zero (a := m3Data.den) (by decide)
  · exact expand_ne_zero (a := u3Data.den) (by decide)
  · exact expand_ne_zero (a := v3Data.den) (by decide)
  · exact expand_ne_zero (a := m6Data.den) (by decide)
  · exact expand_ne_zero (a := u6Data.den) (by decide)
  · exact expand_ne_zero (a := v6Data.den) (by decide)
  · exact expand_ne_zero (a := mFData.den) (by decide)
  · exact expand_ne_zero (a := v3Data.num) (by decide)
  · have h₁ : (unitData - u2Data).toFraction.num ≠ 0 :=
      expand_ne_zero (a := (unitData - u2Data).num) (by decide)
    simpa only [toFraction_sub, unitData, toFraction_scalar, unit, u2] using h₁
  · have h₁ : (unitData - rotatedSixData).toFraction.num ≠ 0 :=
      expand_ne_zero (a := (unitData - rotatedSixData).num) (by decide)
    simpa only [toFraction_sub, rotatedSixData, toFraction_mul, unitData, toFraction_scalar, unit,
      rotatedSixX, u6] using h₁

end
end ManuscriptAudit.Paper5OrdinaryThirtyOneCertificates

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5OrdinaryThirtyOneCertificates.slope_two,
      ``ManuscriptAudit.Paper5OrdinaryThirtyOneCertificates.x_two,
      ``ManuscriptAudit.Paper5OrdinaryThirtyOneCertificates.y_two,
      ``ManuscriptAudit.Paper5OrdinaryThirtyOneCertificates.slope_three,
      ``ManuscriptAudit.Paper5OrdinaryThirtyOneCertificates.x_three,
      ``ManuscriptAudit.Paper5OrdinaryThirtyOneCertificates.y_three,
      ``ManuscriptAudit.Paper5OrdinaryThirtyOneCertificates.slope_six,
      ``ManuscriptAudit.Paper5OrdinaryThirtyOneCertificates.x_six,
      ``ManuscriptAudit.Paper5OrdinaryThirtyOneCertificates.y_six,
      ``ManuscriptAudit.Paper5OrdinaryThirtyOneCertificates.slope_frobenius,
      ``ManuscriptAudit.Paper5OrdinaryThirtyOneCertificates.x_frobenius,
      ``ManuscriptAudit.Paper5OrdinaryThirtyOneCertificates.y_frobenius,
      ``ManuscriptAudit.Paper5OrdinaryThirtyOneCertificates.excluded_nonzero] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"

