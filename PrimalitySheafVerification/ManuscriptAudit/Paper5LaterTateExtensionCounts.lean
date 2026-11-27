import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper5LaterAllTatePowers
import PrimalitySheafVerification.ManuscriptAudit.Paper5PrintedActualExtensionCounts
import PrimalitySheafVerification.ManuscriptAudit.Paper5LaterPointCounts

/-! Actual extension point counts give all later-table Tate power traces over finite extensions. -/

namespace ManuscriptAudit.Paper5LaterTateExtensionCounts

open Paper5LaterTables Paper5LaterAllTatePowers PowerTateModule CubicFrobeniusSexticTwists
open CubicNonsplitTwoThreeAdicCharpoly Paper5PrintedSupersingular Paper5NonsplitFrobeniusModFour
open PrimalitySheafVerification.ManuscriptAudit (paper5TraceCurve)

noncomputable section

theorem row_signed_point_count {r : TateRow} (hr : r ∈ tateRows) :
    (r.prime : ℤ) + 1 -
      (Nat.card (paper5TraceCurve r.prime (4 : ZMod r.prime)).toProjective.Point : ℤ) = r.trace := by
  rw [tate_integer_columns] at hr
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
  exact Paper5LaterPointCounts.actual_traces_A4 hc

private theorem good_row_prime_bound : ∀ r ∈ tateRows, 5 ≤ r.prime := by decide

theorem native_trace_det_at_every_finite_extension {r : TateRow} [Fact r.prime.Prime]
    (hr : r ∈ tateRows) (L : Type*) [Field L] [Algebra (ZMod r.prime) L]
    [IsAlgClosed L] [DecidableEq L]
    (E : Type*) [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod r.prime) E]
    (l : ℕ) [Fact l.Prime] (hl : l = 2 ∨ l = 3) :
    let F := endMap l (arithmeticFrobenius (ZMod r.prime) L 4)
    let n := Module.finrank (ZMod r.prime) E
    LinearMap.trace ℤ_[l] (Tate l (Geometric (ZMod r.prime) L 4)) (F^n) =
      ((Fintype.card E : ℤ) + 1 -
        (Nat.card ((paper5TraceCurve r.prime (4 : ZMod r.prime)).baseChange E).toProjective.Point : ℤ)
        : ℤ_[l]) ∧
    LinearMap.det (F^n) = (Fintype.card E : ℤ_[l]) := by
  let n := Module.finrank (ZMod r.prime) E
  have hp := good_row_prime_bound r hr
  obtain ⟨h₂, _⟩ := small_char r.prime (ZMod r.prime) hp
  have h₄ : (4 : ZMod r.prime) ≠ 0 := by
    rw [show (4 : ZMod r.prime) = (2 : ZMod r.prime)^2 by ring]
    exact pow_ne_zero _ h₂
  have hCount := Paper5PrintedActualExtensionCounts.actual_extension_trace_eq_recurrence
    (E := E) hp h₄
  rw [row_signed_point_count hr] at hCount
  obtain ⟨ht, hd⟩ := trace_det_of_every_power (L := L) hr l hl n
  refine ⟨ht.trans (congrArg (fun z : ℤ => (z : ℤ_[l])) hCount.symm), ?_⟩
  have hq : Fintype.card E = r.prime^n := by
    rw [Module.card_eq_pow_finrank (K := ZMod r.prime) (V := E), ZMod.card]
  rw [hq]
  exact hd

end
end ManuscriptAudit.Paper5LaterTateExtensionCounts

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5LaterTateExtensionCounts.row_signed_point_count,
      ``ManuscriptAudit.Paper5LaterTateExtensionCounts.native_trace_det_at_every_finite_extension] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
