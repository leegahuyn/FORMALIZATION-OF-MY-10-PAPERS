import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8ExteriorPrincipal
import PrimalitySheafVerification.ManuscriptAudit.Paper8InsideComplexComparison

/-! The principal exterior branch extends the existing real normalization. -/

namespace ManuscriptAudit.Paper8ExteriorComplexComparison

open Paper8InsideComplexAnalytic Paper8InsideComplexComparison Paper8ExteriorPrincipal
open Paper8ExteriorNormalization (normalizedG ramanujanF ramanujanTerm exterior_summable)

noncomputable section

private theorem standardTerm_ofReal (q : ℝ) (n : ℕ) :
    ((ramanujanTerm q n : ℝ) : ℂ) = standardTerm n (q : ℂ) := by
  rw [ramanujanTerm, standardTerm, pochhammer_ofReal, Complex.ofReal_div,
    Complex.ofReal_pow, Complex.ofReal_pow]

theorem standard_ofReal_inverse {q : ℝ} (hq : 0 < q) (h₁ : q < 1) :
    standard (q : ℂ)⁻¹ = (ramanujanF q⁻¹ : ℂ) := by
  have h := Complex.ofRealCLM.hasSum (exterior_summable hq h₁).hasSum
  change HasSum (fun n => ((ramanujanTerm q⁻¹ n : ℝ) : ℂ)) (ramanujanF q⁻¹ : ℂ) at h
  simp only [standardTerm_ofReal, Complex.ofReal_inv] at h
  exact h.tsum_eq

theorem principal_normalization_ofReal {q : ℝ} (hq : 0 < q) (h₁ : q < 1) :
    principalNormalization (q : ℂ) = (normalizedG q⁻¹ : ℂ) := by
  have hSlit : (q : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.mpr hq
  have hNorm : ‖(q : ℂ)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq] using h₁
  rw [principal_normalization_eq_literal hSlit hNorm, standard_ofReal_inverse hq h₁,
    normalizedG, Complex.ofReal_mul]
  have hExp : (((-(1 : ℝ) / 24 : ℝ) : ℂ)) = -((24 : ℂ)⁻¹) := by norm_num
  rw [Complex.ofReal_cpow (inv_nonneg.mpr hq.le), Complex.ofReal_inv, hExp]

end
end ManuscriptAudit.Paper8ExteriorComplexComparison

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ExteriorComplexComparison.standard_ofReal_inverse,
      ``ManuscriptAudit.Paper8ExteriorComplexComparison.principal_normalization_ofReal] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
