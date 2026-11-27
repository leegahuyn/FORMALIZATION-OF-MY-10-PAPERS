import Lean.Util.CollectAxioms
import Mathlib.Data.ZMod.Basic
import PrimalitySheafVerification.ManuscriptAudit.CubicFractionCoordinateRules

/-! Exact polynomial certificates for the native characteristic-thirty-one addition chain. -/

namespace ManuscriptAudit.Paper5OrdinaryThirtyOneCertificates

open Polynomial CubicFractionCertificates CubicFractionCoordinateRules
open Fraction

noncomputable section

def ofCoeffs (a : List (ZMod 31)) : (ZMod 31)[X] :=
  a.foldr (fun c f => C c + X * f) 0

def unit : Fraction (ZMod 31) := scalar 1

def m2 : Fraction (ZMod 31) := ⟨ofCoeffs [0, -14], ofCoeffs [1, 1]⟩

def u2 : Fraction (ZMod 31) := ⟨ofCoeffs [-2, 8], ofCoeffs [1, 1]⟩

def v2 : Fraction (ZMod 31) := ⟨ofCoeffs [-1, -13, 4], ofCoeffs [1, 2, 1]⟩

def m3 : Fraction (ZMod 31) := ⟨ofCoeffs [13, -11, -4], ofCoeffs [4, 5, 1]⟩

def u3 : Fraction (ZMod 31) := ⟨ofCoeffs [14, -5, 10, 7], ofCoeffs [0, -15, 8, 1]⟩

def v3 : Fraction (ZMod 31) := ⟨ofCoeffs [4, -13, 10, 7, -8], ofCoeffs [0, 2, -14, 12, 1]⟩

def m6 : Fraction (ZMod 31) := ⟨ofCoeffs [2, 3, -1, 13, 6, -3, -15], ofCoeffs [-2, 4, -9, -12, 10, 8, 1]⟩

def u6 : Fraction (ZMod 31) := ⟨ofCoeffs [-3, -9, 10, 10, -8, 0, -5, 4, 8, 1, -11, 3, -6], ofCoeffs [0, 4, 11, 10, -3, 10, 6, -13, 9, 5, 7, 15, 1]⟩

def v6 : Fraction (ZMod 31) := ⟨ofCoeffs [-2, -9, -5, 11, -12, 12, 5, -13, 7, -3, 3, -15, -10, 10, 8, -13, -13, 8, -1], ofCoeffs [0, -8, -6, -12, -8, 3, 15, 2, 3, 2, 1, -10, -11, -13, -8, 13, 13, -8, 1]⟩

def mF : Fraction (ZMod 31) := ⟨ofCoeffs [-4, 9, -13, 2, 0, 0, -1, -7, -7, 13, 8, -1], ofCoeffs [-2, 4, -9, -12, 10, 8, 1]⟩

def rotatedSixX : Fraction (ZMod 31) := scalar 5 * u6

def frobeniusX : Fraction (ZMod 31) := polynomial (X ^ 10)

def frobeniusY : Fraction (ZMod 31) := polynomial ((X + 1) ^ 15)

set_option maxRecDepth 40000
set_option maxHeartbeats 3000000

theorem slope_two : (tangentFraction 1 unit unit).CrossEq m2 := by decide
theorem x_two : (xFraction 1 unit unit m2).CrossEq u2 := by decide
theorem y_two : (yFraction unit unit u2 m2).CrossEq v2 := by decide

theorem slope_three : (secantFraction unit unit u2 v2).CrossEq m3 := by decide
theorem x_three : (xFraction 1 unit u2 m3).CrossEq u3 := by decide
theorem y_three : (yFraction unit unit u3 m3).CrossEq v3 := by decide

theorem slope_six : (tangentFraction 1 u3 v3).CrossEq m6 := by decide
theorem x_six : (xFraction 1 u3 u3 m6).CrossEq u6 := by decide
theorem y_six : (yFraction u3 v3 u6 m6).CrossEq v6 := by decide

theorem slope_frobenius : (secantFraction unit unit rotatedSixX v6).CrossEq mF := by decide
theorem x_frobenius : (xFraction 1 unit rotatedSixX mF).CrossEq frobeniusX := by decide
theorem y_frobenius : (yFraction unit unit frobeniusX mF).CrossEq frobeniusY := by decide

def excluded : List ((ZMod 31)[X]) :=
  [X, X + 1, m2.den, u2.den, v2.den, m3.den, u3.den, v3.den, m6.den, u6.den, v6.den, mF.den,
    v3.num, (unit - u2).num, (unit - rotatedSixX).num]

theorem excluded_nonzero : ∀ f ∈ excluded, f ≠ 0 := by
  intro f h
  simp only [excluded, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

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
