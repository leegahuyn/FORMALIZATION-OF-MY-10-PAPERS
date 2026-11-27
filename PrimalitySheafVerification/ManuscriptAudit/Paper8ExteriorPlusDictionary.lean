import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8PartialThetaDefinitions

/-!
# A counterexample to the unweighted plus relation on physical p. 335

The positive-index Kronecker series and the product correction on this
page give `2ψ+S`. At `q=2^(-24)` this exceeds the actual unweighted
reciprocal series with the squared finite denominator.
-/

namespace ManuscriptAudit.Paper8ExteriorPlusDictionary

open Paper8ExteriorNormalization (ramanujanF)
open Paper8ExteriorProductCorrection Paper8PartialThetaDefinitions

theorem correctionNumerator_eq_one_sub_triangular {q : ℝ} (hq : 0 < q) (h₁ : q < 1) :
    (∑' n : ℕ, correctionNumeratorTerm q n) = 1 - triangularTheta q := by
  have hNorm : Summable (fun n => ‖correctionNumeratorTerm q n‖) := by
    simpa only [Real.norm_eq_abs] using correctionNumerator_summable_abs hq h₁
  have hZero : correctionNumeratorTerm q 0 = 1 := by simp [correctionNumeratorTerm]
  rw [hNorm.of_norm.tsum_eq_zero_add, hZero]
  unfold triangularTheta
  simp_rw [triangularTerm_eq_neg_correction]
  rw [tsum_neg, sub_neg_eq_add]

theorem p335_unweighted_exterior_lt_printed_plus :
    ramanujanF testQ⁻¹ < 2 * unilateralTheta testQ + productCorrection testQ := by
  have hq : 0 < testQ := by norm_num [testQ]
  have h₁ : testQ < 1 := by norm_num [testQ]
  have hGeom : (1 - testQ)⁻¹ < (10 : ℝ) / 9 := by norm_num [testQ]
  have hThetaBound : testQ / (1 - testQ) < 1 := by norm_num [testQ]
  have hTheta : triangularTheta testQ < 1 :=
    ((le_abs_self _).trans (triangularTheta_abs_le hq h₁)).trans_lt hThetaBound
  have hCorrection : 0 ≤ productCorrection testQ := by
    unfold productCorrection
    rw [correctionNumerator_eq_one_sub_triangular hq h₁]
    exact div_nonneg (sub_nonneg.mpr hTheta.le) (sq_nonneg _)
  have hExterior := (exterior_le_geometric hq h₁).trans_lt hGeom
  linarith only [hExterior, hCorrection, unilateralTheta_testQ_ge]

theorem paper8_p335_unweighted_plus_refuted :
    ramanujanF testQ⁻¹ ≠ 2 * unilateralTheta testQ + productCorrection testQ :=
  p335_unweighted_exterior_lt_printed_plus.ne

end ManuscriptAudit.Paper8ExteriorPlusDictionary

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ExteriorPlusDictionary.correctionNumerator_eq_one_sub_triangular,
      ``ManuscriptAudit.Paper8ExteriorPlusDictionary.p335_unweighted_exterior_lt_printed_plus,
      ``ManuscriptAudit.Paper8ExteriorPlusDictionary.paper8_p335_unweighted_plus_refuted] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
