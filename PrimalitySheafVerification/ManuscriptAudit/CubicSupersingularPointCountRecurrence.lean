import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicSupersingularAllFiniteFields

/-! The actual extension point counts satisfy the integral Frobenius recurrence. -/

namespace ManuscriptAudit.CubicSupersingularPointCountRecurrence

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionCard
open PowerTateModule CubicNonsplitThreeAdicTrace Paper5LinearTraceRecurrence
open CubicSupersingularAllFiniteFields

noncomputable section

def signedCount (F : Type*) [Field F] [Fintype F] [DecidableEq F] (A : F) : ℤ :=
  (Fintype.card F : ℤ) + 1 - (Nat.card (shortCubic (0 : F) A).toProjective.Point : ℤ)

variable (p : ℕ) [Fact p.Prime]
variable (F E : Type*) [Field F] [Field E]
variable [Fintype F] [Fintype E] [DecidableEq F] [DecidableEq E]
variable [Algebra (ZMod p) F] [Algebra (ZMod p) E]
variable [CharP F p] [CharP E p] [Algebra F E] [IsScalarTower (ZMod p) F E]
theorem signed_count_eq_recurrence (L : Type*) [Field L] [DecidableEq L]
    [Algebra F L] [Algebra E L] [IsScalarTower F E L] [Algebra (ZMod p) L]
    [IsAlgClosed L] [Algebra.IsAlgebraic (ZMod p) L]
    (hp : 5 ≤ p) (hP : p % 3 = 2) {A : F} (hA : A ≠ 0) :
    signedCount E (algebraMap F E A) =
      Paper5PrintedRecurrence.recurrence (Fintype.card F) (signedCount F A) (Module.finrank F E) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h₂ : 2 ≠ p := by omega
  let B := CubicSupersingularTatePointCount.tateBasis p L 2 F hp hP h₂ hA
  let T := endMap 2 (arithmeticPointFrobenius F L A)
  have ht : LinearMap.trace ℤ_[2] (Tate 2 (GeometricPoints F L A)) T = (signedCount F A : ℤ_[2]) := by
    simpa only [Module.finrank_self, pow_one, Algebra.algebraMap_self_apply, signedCount] using
      arithmetic_power_trace p 2 F F L hp hP h₂ hA
  have hd : LinearMap.det T = (Fintype.card F : ℤ_[2]) :=
    arithmetic_determinant p 2 F L hp hP h₂ hA
  have hpowers := trace_pow_eq_recurrence B T (Fintype.card F) (signedCount F A) ht hd
    (Module.finrank F E)
  have hcount := arithmetic_power_trace p 2 F E L hp hP h₂ hA
  exact (show Function.Injective (Int.cast : ℤ → ℤ_[2]) from Int.cast_injective)
    (hcount.symm.trans hpowers)

end
end ManuscriptAudit.CubicSupersingularPointCountRecurrence

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicSupersingularPointCountRecurrence.signed_count_eq_recurrence
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
