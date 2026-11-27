import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicCoordinateChain
import PrimalitySheafVerification.ManuscriptAudit.CubicExecutableFractions

/-! Executable cross-products and nonzero guards compile into a certified coordinate chain. -/

namespace ManuscriptAudit.CubicExecutableCoordinateChain

open Polynomial CubicCoordinateChain CubicFractionCertificates CubicFractionCoordinateRules
open CubicExecutableFractions
open CoefficientFraction
open CubicCoefficientArithmetic (AllZero expand_ne_zero)

noncomputable section

variable {k : Type*} [CommRing k]

/-- The arithmetic tests needed to certify a finite centered-cubic point computation. -/
set_option maxHeartbeats 1600000 in
inductive Program (A z : k) : Term → CoefficientFraction k → CoefficientFraction k → Type _
  | identity : Program A z .identity (scalar 1) (scalar 1)
  | double {f : Term} {u v m U V : CoefficientFraction k}
      (step : Program A z f u v)
      (hm : Check (tangent A u v) m)
      (hU : Check (nextX A u u m) U)
      (hV : Check (nextY u v U m) V)
      (hn : ¬AllZero v.num) (hmd : ¬AllZero m.den)
      (hUd : ¬AllZero U.den) (hVd : ¬AllZero V.den) :
      Program A z (.double f) U V
  | add {f g : Term} {u₁ v₁ u₂ v₂ m U V : CoefficientFraction k}
      (left : Program A z f u₁ v₁) (right : Program A z g u₂ v₂)
      (hm : Check (secant u₁ v₁ u₂ v₂) m)
      (hU : Check (nextX A u₁ u₂ m) U)
      (hV : Check (nextY u₁ v₁ U m) V)
      (hn : ¬AllZero (u₁ - u₂).num) (hmd : ¬AllZero m.den)
      (hUd : ¬AllZero U.den) (hVd : ¬AllZero V.den) :
      Program A z (.add f g) U V
  | rotate {f : Term} {u v : CoefficientFraction k} (step : Program A z f u v) :
      Program A z (.rotate f) (scalar z * u) v
  | neg {f : Term} {u v : CoefficientFraction k} (step : Program A z f u v) :
      Program A z (.neg f) u (-v)

variable [IsDomain k]

set_option maxHeartbeats 1000000 in
/-- Kernel-computed coefficient tests soundly give every rational equality and nonzero guard. -/
theorem compiles {A z : k} {t : Term} {u v : CoefficientFraction k} (program : Program A z t u v) :
    ∃ chain : Chain A z t u.toFraction v.toFraction, ∀ f ∈ chain.guards, f ≠ 0 := by
  induction program with
  | identity =>
    rw [toFraction_scalar]
    exact ⟨Chain.identity, by simp [Chain.guards]⟩
  | @double f u v m U V step hm hU hV hn hmd hUd hVd ih =>
    obtain ⟨step', hStep⟩ := ih
    have hm' : (tangentFraction A u.toFraction v.toFraction).CrossEq m.toFraction := by
      simpa only [toFraction_tangent] using check_sound hm
    have hU' : (xFraction A u.toFraction u.toFraction m.toFraction).CrossEq U.toFraction := by
      simpa only [toFraction_nextX] using check_sound hU
    have hV' : (yFraction u.toFraction v.toFraction U.toFraction m.toFraction).CrossEq V.toFraction := by
      simpa only [toFraction_nextY] using check_sound hV
    refine ⟨Chain.double step' hm' hU' hV', ?_⟩
    intro q hq
    change q ∈ step'.guards ++ [v.toFraction.num, m.toFraction.den, U.toFraction.den,
      V.toFraction.den] at hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hStep q hq
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact CubicCoefficientArithmetic.expand_ne_zero hn
      · exact CubicCoefficientArithmetic.expand_ne_zero hmd
      · exact CubicCoefficientArithmetic.expand_ne_zero hUd
      · exact CubicCoefficientArithmetic.expand_ne_zero hVd
  | @add f g u₁ v₁ u₂ v₂ m U V left right hm hU hV hn hmd hUd hVd ih₁ ih₂ =>
    obtain ⟨left', hLeft⟩ := ih₁
    obtain ⟨right', hRight⟩ := ih₂
    have hm' : (secantFraction u₁.toFraction v₁.toFraction u₂.toFraction v₂.toFraction).CrossEq
        m.toFraction := by simpa only [toFraction_secant] using check_sound hm
    have hU' : (xFraction A u₁.toFraction u₂.toFraction m.toFraction).CrossEq U.toFraction := by
      simpa only [toFraction_nextX] using check_sound hU
    have hV' : (yFraction u₁.toFraction v₁.toFraction U.toFraction m.toFraction).CrossEq V.toFraction := by
      simpa only [toFraction_nextY] using check_sound hV
    refine ⟨Chain.add left' right' hm' hU' hV', ?_⟩
    intro q hq
    change q ∈ (left'.guards ++ right'.guards) ++ [(u₁.toFraction - u₂.toFraction).num,
      m.toFraction.den, U.toFraction.den, V.toFraction.den] at hq
    rcases List.mem_append.mp hq with hq | hq
    · rcases List.mem_append.mp hq with hq | hq
      · exact hLeft q hq
      · exact hRight q hq
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · have h : (u₁ - u₂).toFraction.num ≠ 0 := CubicCoefficientArithmetic.expand_ne_zero hn
        simpa only [toFraction_sub] using h
      · exact CubicCoefficientArithmetic.expand_ne_zero hmd
      · exact CubicCoefficientArithmetic.expand_ne_zero hUd
      · exact CubicCoefficientArithmetic.expand_ne_zero hVd
  | @rotate f u v step ih =>
    obtain ⟨step', hStep⟩ := ih
    rw [toFraction_mul, toFraction_scalar]
    exact ⟨Chain.rotate step', hStep⟩
  | @neg f u v step ih =>
    obtain ⟨step', hStep⟩ := ih
    rw [toFraction_neg]
    exact ⟨Chain.neg step', hStep⟩

end
end ManuscriptAudit.CubicExecutableCoordinateChain

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicExecutableCoordinateChain.compiles
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
