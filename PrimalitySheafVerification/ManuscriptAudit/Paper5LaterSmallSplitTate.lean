import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicFrobeniusSexticTwists
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinarySevenTwistTate
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryThirteenTwistTate
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryNineteenTwistTate

/-! The three small later A = 4 rows specialize the checked native all-twist computations. -/

namespace ManuscriptAudit.Paper5LaterSmallSplitTate

open CubicFrobeniusSexticTwists PowerTateModule

noncomputable section

section P7

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

variable (L : Type*) [Field L] [Algebra (ZMod 7) L] [CharP L 7] [IsAlgClosed L] [DecidableEq L]

theorem trace_det_7 (l : ℕ) [Fact l.Prime] (hl : l = 2 ∨ l = 3) :
    LinearMap.trace ℤ_[l] (Tate l (Geometric (ZMod 7) L 4))
      (endMap l (arithmeticFrobenius (ZMod 7) L 4)) = 5 ∧
    LinearMap.det (endMap l (arithmeticFrobenius (ZMod 7) L 4)) = 7 := by
  have h4 : (4 : ZMod 7) ≠ 0 := by decide
  have h := Paper5OrdinarySevenTwistTate.trace_det L l hl 4 h4
  have hRow : (Paper5OrdinarySevenTwistParameters.row (4 : ZMod 7)).trace = 5 := by decide
  rw [hRow] at h
  simpa only [Int.cast_neg, Int.cast_ofNat, Int.cast_one] using h

end P7

section P13

local instance : Fact (Nat.Prime 13) := ⟨by decide⟩

variable (L : Type*) [Field L] [Algebra (ZMod 13) L] [CharP L 13] [IsAlgClosed L] [DecidableEq L]

theorem trace_det_13 (l : ℕ) [Fact l.Prime] (hl : l = 2 ∨ l = 3) :
    LinearMap.trace ℤ_[l] (Tate l (Geometric (ZMod 13) L 4))
      (endMap l (arithmeticFrobenius (ZMod 13) L 4)) = -7 ∧
    LinearMap.det (endMap l (arithmeticFrobenius (ZMod 13) L 4)) = 13 := by
  have h4 : (4 : ZMod 13) ≠ 0 := by decide
  have h := Paper5OrdinaryThirteenTwistTate.trace_det L l hl 4 h4
  have hRow : (Paper5OrdinaryThirteenTwistParameters.row (4 : ZMod 13)).trace = -7 := by decide
  rw [hRow] at h
  simpa only [Int.cast_neg, Int.cast_ofNat, Int.cast_one] using h

end P13

section P19

local instance : Fact (Nat.Prime 19) := ⟨by decide⟩

variable (L : Type*) [Field L] [Algebra (ZMod 19) L] [CharP L 19] [IsAlgClosed L] [DecidableEq L]

theorem trace_det_19 (l : ℕ) [Fact l.Prime] (hl : l = 2 ∨ l = 3) :
    LinearMap.trace ℤ_[l] (Tate l (Geometric (ZMod 19) L 4))
      (endMap l (arithmeticFrobenius (ZMod 19) L 4)) = -1 ∧
    LinearMap.det (endMap l (arithmeticFrobenius (ZMod 19) L 4)) = 19 := by
  have h4 : (4 : ZMod 19) ≠ 0 := by decide
  have h := Paper5OrdinaryNineteenTwistTate.trace_det L l hl 4 h4
  have hRow : (Paper5OrdinaryNineteenTwistParameters.row (4 : ZMod 19)).trace = -1 := by decide
  rw [hRow] at h
  simpa only [Int.cast_neg, Int.cast_ofNat, Int.cast_one] using h

end P19

end
end ManuscriptAudit.Paper5LaterSmallSplitTate

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5LaterSmallSplitTate.trace_det_7,
      ``ManuscriptAudit.Paper5LaterSmallSplitTate.trace_det_13,
      ``ManuscriptAudit.Paper5LaterSmallSplitTate.trace_det_19] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
