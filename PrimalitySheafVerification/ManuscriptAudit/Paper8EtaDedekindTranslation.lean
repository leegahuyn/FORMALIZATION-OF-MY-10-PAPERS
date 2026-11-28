import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaPositiveLowerLeftMultiplier
import PrimalitySheafVerification.ManuscriptAudit.Paper8ActualEtaTranslation
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossCuspPhase

/-! The actual eta multiplier and the Dedekind candidate have the same right-translation law. -/

namespace ManuscriptAudit.Paper8EtaDedekindTranslation

open Matrix
open Paper8EtaPositiveLowerLeftMultiplier Paper8ActualEtaTranslation Paper8OddCrossCuspPhase
open Paper8HolomorphicPartPhase (periodCoefficient)
open scoped MatrixGroups

theorem right_T_entries (g : SL(2, ℤ)) (m : ℤ) :
    (g * ModularGroup.T ^ m) 0 0 = g 0 0 ∧
    (g * ModularGroup.T ^ m) 1 0 = g 1 0 ∧
    (g * ModularGroup.T ^ m) 1 1 = g 1 1 + g 1 0 * m := by
  change (g.1 * (ModularGroup.T ^ m).1) 0 0 = g 0 0 ∧
    (g.1 * (ModularGroup.T ^ m).1) 1 0 = g 1 0 ∧
    (g.1 * (ModularGroup.T ^ m).1) 1 1 = g 1 1 + g 1 0 * m
  rw [ModularGroup.coe_T_zpow]
  simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm, mul_comm]

def translationPhase (m : ℤ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) / 24)

theorem principalEtaMultiplier_mul_T (g : SL(2, ℤ)) (hg : 0 < g 1 0) (m : ℤ) :
    principalEtaMultiplier (g * ModularGroup.T ^ m) =
      translationPhase m * principalEtaMultiplier g := by
  obtain ⟨ha, hc, hd⟩ := right_T_entries g m
  have hT : 0 < (g * ModularGroup.T ^ m) 1 0 := by rwa [hc]
  let c : ℂ := g 1 0
  let z : ℂ := (-(g 1 1 : ℂ) + Complex.I) / c
  have hc₀ : c ≠ 0 := by exact_mod_cast hg.ne'
  have hZ : (-((g 1 1 + g 1 0 * m : ℤ) : ℂ) + Complex.I) / c = z + ((-m : ℤ) : ℂ) := by
    push_cast
    dsimp only [z]
    change (-(↑(g 1 1) + c * (m : ℂ)) + Complex.I) / c =
      (-(g 1 1 : ℂ) + Complex.I) / c + -(m : ℂ)
    field_simp [hc₀] <;> ring
  have hExp : translationPhase (-m) = (translationPhase m)⁻¹ := by
    have h : 2 * (Real.pi : ℂ) * Complex.I * ((-m : ℤ) : ℂ) / 24 =
        -(2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) / 24) := by push_cast; ring
    unfold translationPhase
    rw [h, Complex.exp_neg]
  rw [principalEtaMultiplier_at_reference_points _ hT,
    principalEtaMultiplier_at_reference_points _ hg, ha, hc, hd]
  change ModularForm.eta (((g 0 0 : ℂ) + Complex.I) / c) /
      (Complex.sqrt Complex.I * ModularForm.eta ((-((g 1 1 + g 1 0 * m : ℤ) : ℂ) + Complex.I) / c)) =
    translationPhase m * (ModularForm.eta (((g 0 0 : ℂ) + Complex.I) / c) /
      (Complex.sqrt Complex.I * ModularForm.eta z))
  rw [hZ, eta_add_integer]
  change _ / (Complex.sqrt Complex.I * (translationPhase (-m) * ModularForm.eta z)) = _
  rw [hExp]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

theorem explicitEta_add_right {D : ℕ} (hD : 0 < D) (a d m : ℤ) :
    explicitEta D a (d + (D : ℤ) * m) = translationPhase m * explicitEta D a d := by
  have hC : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  unfold explicitEta
  rw [dedekind_translate hD]
  unfold translationPhase integralDiagonal periodCoefficient
  rw [← Complex.exp_add]
  apply congrArg Complex.exp
  push_cast
  field_simp [hC] <;> ring

theorem principalEtaMultiplier_eq_explicitEta_mul_T_iff {D : ℕ} (hD : 0 < D)
    (g : SL(2, ℤ)) (hg : g 1 0 = (D : ℤ)) (m : ℤ) :
    principalEtaMultiplier (g * ModularGroup.T ^ m) =
      explicitEta D ((g * ModularGroup.T ^ m) 0 0) ((g * ModularGroup.T ^ m) 1 1) ↔
    principalEtaMultiplier g = explicitEta D (g 0 0) (g 1 1) := by
  have hp : 0 < g 1 0 := by rw [hg]; exact_mod_cast hD
  obtain ⟨ha, _, hd⟩ := right_T_entries g m
  rw [principalEtaMultiplier_mul_T g hp m, ha, hd, hg, explicitEta_add_right hD]
  constructor
  · exact mul_left_cancel₀ (Complex.exp_ne_zero _)
  · intro h
    rw [h]

end ManuscriptAudit.Paper8EtaDedekindTranslation

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8EtaDedekindTranslation.principalEtaMultiplier_eq_explicitEta_mul_T_iff
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
