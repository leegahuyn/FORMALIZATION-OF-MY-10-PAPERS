import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaCentralSign
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaHalfWeightPhase

/-! The central element distinguishes the admissible odd weight-minus-half phase from a conjugated positive phase. -/

namespace ManuscriptAudit.Paper8EtaOddCenterPhase

open UpperHalfPlane Paper8EtaCentralSign Paper8ActualEtaSquaredModularity
open Paper8EtaHalfWeightPhase Paper8OddCrossCuspRows
open scoped MatrixGroups

private theorem central_denominator (z : ℍ) :
    denominator (centralNeg 4 : SL(2, ℤ)) z = -1 := by
  have h0 : ((centralNeg 4 : SL(2, ℤ)) 1 0) = 0 := by
    change (-(1 : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 = 0
    simp [Matrix.one_apply]
  have h1 : ((centralNeg 4 : SL(2, ℤ)) 1 1) = -1 := by
    change (-(1 : Matrix (Fin 2) (Fin 2) ℤ)) 1 1 = -1
    simp [Matrix.one_apply]
  unfold denominator
  simp only [h0, h1, Int.cast_zero, Int.cast_neg, Int.cast_one, zero_mul, zero_add]

theorem positivePhase_central_element (z : ℍ) :
    positivePhase (centralNeg 4 : SL(2, ℤ)) z = 1 := by
  rw [positivePhase, central_denominator, centralNeg_smul, norm_neg, norm_one,
    Real.sqrt_one, Complex.ofReal_one, mul_one, div_self (ModularForm.eta_ne_zero z.im_pos)]

theorem negativePhase_central_element (z : ℍ) :
    negativePhase (centralNeg 4 : SL(2, ℤ)) z = -1 := by
  rw [negativePhase, positivePhase_central_element, central_denominator, norm_neg, norm_one,
    Complex.ofReal_one, one_mul]
  norm_num

theorem actualOddPhase_central_element (z : ℍ) :
    (levelCharacter (centralNeg 4) : ℂ) * negativePhase (centralNeg 4 : SL(2, ℤ)) z = 1 := by
  rw [levelCharacter_centralNeg, negativePhase_central_element]
  norm_num

theorem conjugatedPositivePhase_odd_section_eq_zero (F : ℍ → ℂ)
    (hF : ∀ (g : CongruenceSubgroup.Gamma0 4) (z : ℍ),
      F ((g : SL(2, ℤ)) • z) =
        (levelCharacter g : ℂ) * (starRingEnd ℂ) (positivePhase (g : SL(2, ℤ)) z) * F z) :
    F = 0 := by
  funext z
  have h := hF (centralNeg 4) z
  rw [centralNeg_smul, levelCharacter_centralNeg, positivePhase_central_element, map_one,
    Int.cast_neg, Int.cast_one, mul_one, neg_one_mul] at h
  change F z = 0
  linear_combination h / 2

end ManuscriptAudit.Paper8EtaOddCenterPhase

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8EtaOddCenterPhase.actualOddPhase_central_element,
      ``ManuscriptAudit.Paper8EtaOddCenterPhase.conjugatedPositivePhase_odd_section_eq_zero] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
