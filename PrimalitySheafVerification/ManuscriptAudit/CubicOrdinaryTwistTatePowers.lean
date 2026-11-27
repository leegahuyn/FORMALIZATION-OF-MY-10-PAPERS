import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import PrimalitySheafVerification.ManuscriptAudit.CubicOrdinaryTwistTateCoefficients
import PrimalitySheafVerification.ManuscriptAudit.CubicExtensionFrobeniusAt
import PrimalitySheafVerification.ManuscriptAudit.CubicSplitExtensionTraceRecurrence
import PrimalitySheafVerification.ManuscriptAudit.Paper5LinearTraceRecurrence

/-! Every further extension has the arithmetic trace on the actual Frobenius power, for an arbitrary ordinary twist. -/

namespace ManuscriptAudit.CubicOrdinaryTwistTatePowers

open Module FiniteFieldPointCount CubicThreeTorsionOrdinate CubicNonsplitFrobeniusTrace
open CubicNonsplitThreeAdicTrace CubicFrobeniusTranscendentalRelation
open PowerTateModule CubicSplitExtensionTraceRecurrence Paper5NonsplitFrobeniusModFour
open scoped Padic

noncomputable section

variable (p : ℕ) [Fact p.Prime] (E D L : Type*) [Field E] [Fintype E] [DecidableEq E]
  [Field D] [Fintype D] [DecidableEq D] [Algebra E D] [Algebra (ZMod p) E]
  [Field L] [DecidableEq L] [IsAlgClosed L] [Algebra E L] [Algebra (ZMod p) L]
variable (l : ℕ) [Fact l.Prime]

private theorem three_dvd_card_sub_one (hs : p % 3 = 1) :
    3 ∣ Fintype.card E - 1 := by
  have hpow (n : ℕ) : p ^ n % 3 = 1 := by
    induction n with
    | zero => decide
    | succ n hn => rw [pow_succ, Nat.mul_mod, hn, hs] <;> decide
  have hCard := Module.card_eq_pow_finrank (K := ZMod p) (V := E)
  rw [ZMod.card] at hCard
  have h := hpow (finrank (ZMod p) E)
  rw [← hCard] at h
  omega

/-- The power for the actual extension degree has the signed count over D and determinant #D. -/
theorem power_trace_det (hp : 5 ≤ p) (hs : p % 3 = 1) (hl : l = 2 ∨ l = 3)
    {A : E} (hA : A ≠ 0) :
    let F := endMap l (arithmeticPointFrobenius E L A) ^ (finrank E D)
    LinearMap.trace ℤ_[l] _ F = (signedTrace (algebraMap E D A) : ℤ_[l]) ∧
      LinearMap.det F = (Fintype.card D : ℤ_[l]) := by
  let F := endMap l (arithmeticPointFrobenius E L A)
  obtain ⟨ht, hd⟩ := CubicOrdinaryTwistTateCoefficients.trace_det p E L l hp hs hl hA
  obtain ⟨h₂, h₃⟩ := small_char p E hp
  obtain ⟨h₂L, h₃L⟩ := small_char p L hp
  let B := CubicOrdinaryTwistTateCoefficients.centeredBasis L l h₂L h₃L
    ((map_ne_zero (algebraMap E L)).mpr hA) hl
  have hAri := extension_trace_eq_recurrence (E := D) h₂ h₃ hA (three_dvd_card_sub_one p E hs)
  change signedTrace (algebraMap E D A) =
    Paper5PrintedRecurrence.recurrence (Fintype.card E) (arithmeticTrace E A) (finrank E D) at hAri
  have hTr := Paper5LinearTraceRecurrence.trace_pow_eq_recurrence B F (Fintype.card E)
    (arithmeticTrace E A) ht hd (finrank E D)
  constructor
  · exact hTr.trans (congrArg (fun z : ℤ => (z : ℤ_[l])) hAri.symm)
  · change LinearMap.det (F ^ (finrank E D)) = (Fintype.card D : ℤ_[l])
    rw [map_pow, hd, Module.card_eq_pow_finrank (K := E) (V := D), Nat.cast_pow]

variable [Algebra D L] [IsScalarTower E D L]

/-- The actual relative Frobenius on the same geometric curve is that exact native power. -/
theorem actual_relative_eq_power (A : E) :
    endMap l (pointMapAt D L (Curve (algebraMap E D A)) (Curve (algebraMap E L A))
      ((centered_baseChange D L _).trans (congrArg Curve (IsScalarTower.algebraMap_apply E D L A).symm))
      (FiniteField.frobeniusAlgHom D L)) =
      endMap l (arithmeticPointFrobenius E L A) ^ finrank E D := by
  have h := CubicExtensionFrobeniusAt.point_eq_pow E D L (finrank E D) A
    (IsScalarTower.algebraMap_apply E D L A).symm (Module.card_eq_pow_finrank (K := E) (V := D))
  rw [h, map_pow]

end

end ManuscriptAudit.CubicOrdinaryTwistTatePowers

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.CubicOrdinaryTwistTatePowers.power_trace_det,
      ``ManuscriptAudit.CubicOrdinaryTwistTatePowers.actual_relative_eq_power] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
