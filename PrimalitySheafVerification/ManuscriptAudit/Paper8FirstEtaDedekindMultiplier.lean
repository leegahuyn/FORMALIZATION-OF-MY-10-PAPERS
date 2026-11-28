import Lean.Util.CollectAxioms
import Mathlib.Analysis.RCLike.Sqrt
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaPositiveLowerLeftMultiplier
import PrimalitySheafVerification.ManuscriptAudit.Paper8ActualEtaTranslation
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossCuspPhase

/-! At lower-left entry one, the actual eta multiplier equals the arithmetic phase used in Paper 8. -/

namespace ManuscriptAudit.Paper8FirstEtaDedekindMultiplier

open Paper8EtaPositiveLowerLeftMultiplier Paper8ActualEtaTranslation
open Paper8OddCrossCuspPhase
open Paper8ContourResidueWeights (dedekindSum sawtooth)
open Paper8HolomorphicPartPhase (periodCoefficient)
open scoped MatrixGroups

private theorem dedekindSum_one (d : ℤ) : dedekindSum d 1 = 0 := by
  norm_num [dedekindSum, Fin.sum_univ_one, sawtooth]

theorem principalEtaMultiplier_eq_explicitEta_of_lowerLeft_one (g : SL(2, ℤ))
    (hg : g 1 0 = 1) : principalEtaMultiplier g = explicitEta 1 (g 0 0) (g 1 1) := by
  have hPos : 0 < g 1 0 := by rw [hg]; decide
  have hEtaI : ModularForm.eta Complex.I ≠ 0 :=
    ModularForm.eta_ne_zero (by simp : 0 < Complex.I.im)
  have hAdd (m : ℤ) :
      ModularForm.eta ((m : ℂ) + Complex.I) =
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) / 24) * ModularForm.eta Complex.I := by
    simpa only [add_comm] using eta_add_integer Complex.I m
  rw [principalEtaMultiplier_at_reference_points g hPos, hg]
  simp only [Int.cast_one, div_one]
  rw [hAdd, ← Int.cast_neg, hAdd, sqrt_eq_exp Complex.I_ne_zero, Complex.log_I]
  rw [explicitEta, dedekindSum_one]
  simp only [Rat.cast_zero, zero_div, sub_zero, integralDiagonal, Nat.cast_one, mul_one, periodCoefficient]
  apply (div_eq_iff (mul_ne_zero (Complex.exp_ne_zero _) (mul_ne_zero (Complex.exp_ne_zero _) hEtaI))).2
  simp only [← mul_assoc, ← Complex.exp_add]
  apply congrArg (fun v : ℂ => Complex.exp v * ModularForm.eta Complex.I)
  push_cast
  ring

end ManuscriptAudit.Paper8FirstEtaDedekindMultiplier

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8FirstEtaDedekindMultiplier.principalEtaMultiplier_eq_explicitEta_of_lowerLeft_one
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
