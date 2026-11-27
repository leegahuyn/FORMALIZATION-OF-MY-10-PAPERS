import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicGeometricTorsion
import PrimalitySheafVerification.ManuscriptAudit.CubicThreeFrobeniusCharpoly
import PrimalitySheafVerification.ManuscriptAudit.Paper5PrintedActualExtensionCounts

/-! The actual q-Frobenius on three-torsion gives the 168 printed trace values modulo three. -/

namespace ManuscriptAudit.Paper5FrobeniusModThree

open PrimalitySheafVerification.ManuscriptAudit (paper5TraceCurve)
open CubicGeometricTorsion CubicThreeFrobeniusActual CubicThreeFrobeniusCharpoly
open Paper5PrintedRecurrence Paper5PrintedActualExtensionCounts

noncomputable section

variable {r : Row} [Fact r.prime.Prime]
variable (E : Type*) [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod r.prime) E]
variable (L : Type*) [Field L] [Algebra E L] [DecidableEq L] [IsAlgClosed L]

theorem printedRows_actual_frobenius_trace_det (hr : r ∈ printedRows) (i : Fin 6)
    (hd : Module.finrank (ZMod r.prime) E = i.val + 1) :
    LinearMap.trace (ZMod 3) (ActualTorsion E L (1 : E)) (actualFrobenius E L (1 : E)) =
      ((r.traceColumns[i.val]?).getD 0 : ZMod 3) ∧
    LinearMap.det (actualFrobenius E L (1 : E)) =
      ((r.prime ^ (i.val + 1) : ℕ) : ZMod 3) := by
  letI : CharP E r.prime :=
    charP_of_injective_algebraMap (algebraMap (ZMod r.prime) E).injective r.prime
  have hp := Paper5PrintedSupersingular.printedRows_prime_at_least_five hr
  have hsmall (n : ℕ) (h₀ : 0 < n) (hn : n < r.prime) : (n : E) ≠ 0 :=
    (CharP.cast_eq_zero_iff E r.prime n).not.mpr
      (fun h => (Nat.not_le_of_lt hn) (Nat.le_of_dvd h₀ h))
  have h₂ : (2 : E) ≠ 0 := by
    simpa only [Nat.cast_ofNat] using hsmall 2 (by decide) (by omega)
  have h₃ : (3 : E) ≠ 0 := by
    simpa only [Nat.cast_ofNat] using hsmall 3 (by decide) (by omega)
  have htrace : signedPointTrace E (1 : E) = (r.traceColumns[i.val]?).getD 0 := by
    unfold signedPointTrace
    rw [← map_one (algebraMap (ZMod r.prime) E), ← printed_cubic_baseChange_eq_zero r.prime]
    exact printedRows_actual_extension_trace_at hr i hd
  have hq : Fintype.card E = r.prime ^ (i.val + 1) := by
    rw [Module.card_eq_pow_finrank (K := ZMod r.prime) (V := E), ZMod.card, hd]
  obtain ⟨htr, hdet⟩ := actualFrobenius_arithmetic_trace_det E L h₂ h₃
    (one_ne_zero : (1 : E) ≠ 0)
  exact ⟨htr.trans (congrArg (fun a : ℤ => (a : ZMod 3)) htrace),
    hdet.trans (congrArg (fun q : ℕ => (q : ZMod 3)) hq)⟩

end
end ManuscriptAudit.Paper5FrobeniusModThree

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.Paper5FrobeniusModThree.printedRows_actual_frobenius_trace_det
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
