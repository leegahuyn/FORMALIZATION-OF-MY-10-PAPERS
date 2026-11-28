import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8PrimePowerDigitSum
import PrimalitySheafVerification.ManuscriptAudit.Paper8ZModAdditiveCRT

/-! The weighted stationary sum equals the same sum indexed by the native unit group. -/

namespace ManuscriptAudit.Paper8WeightedUnitSumBridge

open Finset Paper8PrimePowerDigitSum Paper8ProductStationaryPhase Paper8ZModAdditiveCRT
open scoped Classical

noncomputable section

private def subtypeIsUnitEquiv (R : Type*) [Monoid R] : {x : R // IsUnit x} ≃ Rˣ where
  toFun x := x.2.unit
  invFun x := ⟨x, x.isUnit⟩
  left_inv x := Subtype.ext x.2.unit_spec
  right_inv x := Units.ext x.isUnit.unit_spec

theorem weightedSymmetricUnitSum_eq_twisted {n m : ℕ} [NeZero n] [NeZero m]
    (w : ZMod m → ℂ) (a : ZMod (n * m)) :
    weightedSymmetricUnitSum w a =
      twistedSymmetricUnitSum (fun x => w (reduceLowDigit (x : ZMod (n * m)))) a := by
  unfold weightedSymmetricUnitSum weightedSymmetricUnitTerm twistedSymmetricUnitSum symmetricPhase
  rw [← Finset.sum_filter, Finset.sum_subtype (p := fun x : ZMod (n * m) => IsUnit x) _ (by simp)]
  apply Fintype.sum_equiv (subtypeIsUnitEquiv (ZMod (n * m))) _ _
  intro x
  change w (reduceLowDigit x.1) * ZMod.stdAddChar (a * (x.1 + x.1⁻¹)) =
    w (reduceLowDigit (x.2.unit : ZMod (n * m))) *
      ZMod.stdAddChar (a * ((x.2.unit : ZMod (n * m)) + ((x.2.unit⁻¹ : (ZMod (n * m))ˣ) : ZMod (n * m))))
  rw [← ZMod.inv_coe_unit, x.2.unit_spec]

end
end ManuscriptAudit.Paper8WeightedUnitSumBridge

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8WeightedUnitSumBridge.weightedSymmetricUnitSum_eq_twisted
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
