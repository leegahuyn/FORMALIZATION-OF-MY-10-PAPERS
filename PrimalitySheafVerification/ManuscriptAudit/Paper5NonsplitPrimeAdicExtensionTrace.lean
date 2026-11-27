import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicNonsplitTwoThreeAdicCharpoly
import PrimalitySheafVerification.ManuscriptAudit.Paper5LinearTraceRecurrence
import PrimalitySheafVerification.ManuscriptAudit.Paper5NonsplitFrobeniusModFour

/-! The actual prime-adic powers of Frobenius match Paper 5's finite-field point counts. -/

namespace ManuscriptAudit.Paper5NonsplitPrimeAdicExtensionTrace

open PrimalitySheafVerification.ManuscriptAudit (paper5TraceCurve paper5_traceCurve_trace_eq_zero)
open CubicNonsplitThreeAdicTrace CubicNonsplitPrimeAdicFrobenius CubicNonsplitTwoThreeAdicCharpoly
open Paper5NonsplitFrobeniusModFour Paper5NonsplitExtensionRecurrence Paper5LinearTraceRecurrence
open PowerTateModule Paper5PrintedRecurrence Module

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (D : Type*) [Field D] [Fintype D] [DecidableEq D] [Algebra (ZMod p) D]
variable (L : Type*) [Field L] [Algebra (ZMod p) L] [IsAlgClosed L] [DecidableEq L]
variable (l : ℕ) [Fact l.Prime]

/-- Actual Frobenius on a rank-two Tate module computes the signed count over each finite extension. -/
theorem trace_pow_eq_point_count (hp : 5 ≤ p) (hq : p % 3 = 2) {A : ZMod p} (hA : A ≠ 0)
    (B : Basis (Fin 2) ℤ_[l] (Tate l (GeometricPoints (ZMod p) L A))) :
    LinearMap.trace ℤ_[l] (Tate l (GeometricPoints (ZMod p) L A))
        ((Action (ZMod p) L l A) ^ (Module.finrank (ZMod p) D)) =
      (((Fintype.card D : ℤ) + 1 -
        (Nat.card ((paper5TraceCurve p A).baseChange D).toProjective.Point : ℤ)) : ℤ_[l]) := by
  let E := ZMod p
  have h₂ : (2 : E) ≠ 0 := (small_char p E hp).1
  have h₃ : (3 : E) ≠ 0 := (small_char p E hp).2
  have hq3 : Fintype.card E % 3 = 2 := by simpa only [E, ZMod.card] using hq
  have hq2 : Fintype.card E % 2 = 1 := by
    apply FiniteField.odd_card_of_char_ne_two
    rw [ringChar.eq E p]
    omega
  have ht := actual_prime_adic_trace_zero E L l h₂ h₃ hA hq3
  have hd : LinearMap.det (Action E L l A) = (p : ℤ_[l]) := by
    simpa only [E, ZMod.card] using determinant_eq_card E L l h₂ h₃ hA hq3 hq2 B
  have hTrace := trace_pow_eq_recurrence B (Action E L l A) p 0
    (by simpa only [Int.cast_zero] using ht) hd (Module.finrank (ZMod p) D)
  have hCount := actual_extension_trace_eq_recurrence_of_mod_two (E := D) hp hq hA
  rw [paper5_traceCurve_trace_eq_zero hp hq hA] at hCount
  exact hTrace.trans (congrArg (fun a : ℤ => (a : ℤ_[l])) hCount).symm

end
end ManuscriptAudit.Paper5NonsplitPrimeAdicExtensionTrace

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper5NonsplitPrimeAdicExtensionTrace.trace_pow_eq_point_count
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
