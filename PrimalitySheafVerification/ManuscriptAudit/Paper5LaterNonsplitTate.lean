import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper5PrintedNonsplitTateTraces
import PrimalitySheafVerification.ManuscriptAudit.Paper5LaterTables

/-! The later A = 4 table uses the same native nonsplit Tate action at every prime in that class. -/

namespace ManuscriptAudit.Paper5LaterNonsplitTate

open CubicNonsplitThreeAdicTrace CubicNonsplitPrimeAdicFrobenius CubicNonsplitTwoThreeAdicCharpoly
open PowerTateModule Paper5NonsplitFrobeniusModFour Paper5LaterTables

noncomputable section

theorem data_exact :
    ∀ r ∈ tateRows, r.prime % 3 = 2 → r.trace = 0 ∧ r.determinant = r.prime := by
  decide

variable (p : ℕ) [Fact p.Prime]
variable (L : Type*) [Field L] [Algebra (ZMod p) L] [IsAlgClosed L] [DecidableEq L]

theorem trace_det_nonsplit (hp : 5 ≤ p) (hmod : p % 3 = 2)
    (l : ℕ) [Fact l.Prime] (hl : l = 2 ∨ l = 3) :
    LinearMap.trace ℤ_[l] (Tate l (GeometricPoints (ZMod p) L 4))
      (Action (ZMod p) L l 4) = 0 ∧ LinearMap.det (Action (ZMod p) L l 4) = (p : ℤ_[l]) := by
  obtain ⟨h₂, h₃⟩ := small_char p (ZMod p) hp
  have h₄ : (4 : ZMod p) ≠ 0 := by
    have h : (4 : ZMod p) = (2 : ZMod p)^2 := by ring
    rw [h]
    exact pow_ne_zero _ h₂
  have hq : Fintype.card (ZMod p) % 3 = 2 := by simpa only [ZMod.card] using hmod
  refine ⟨actual_prime_adic_trace_zero (ZMod p) L l h₂ h₃ h₄ hq, ?_⟩
  rcases hl with rfl | rfl
  · simpa only [ZMod.card] using two_adic_determinant (ZMod p) L h₂ h₃ h₄ hq
  · simpa only [ZMod.card] using three_adic_determinant (ZMod p) L h₂ h₃ h₄ hq

end
end ManuscriptAudit.Paper5LaterNonsplitTate

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5LaterNonsplitTate.data_exact,
      ``ManuscriptAudit.Paper5LaterNonsplitTate.trace_det_nonsplit] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
