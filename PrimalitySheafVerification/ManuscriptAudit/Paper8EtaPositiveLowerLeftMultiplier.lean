import Lean.Util.CollectAxioms
import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Tactic.LinearCombination
import PrimalitySheafVerification.ManuscriptAudit.Paper8ActualEtaPowerModularity
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaRigidity

/-!
# The actual principal eta multiplier at positive lower-left entry

The native half-weight transformation has a constant principal-root
multiplier. At the two equal-height rational points determined by the
matrix, the denominator is exactly i, giving an explicit analytic
formula for the same multiplier.
-/

namespace ManuscriptAudit.Paper8EtaPositiveLowerLeftMultiplier

open Set UpperHalfPlane
open Paper8ActualEtaSquaredModularity
open scoped MatrixGroups Manifold

noncomputable section

private theorem complex_sqrt_sq (w : ℂ) : Complex.sqrt w ^ 2 = w := by
  unfold Complex.sqrt
  have hExp : ((2 : ℕ) : ℂ) * (2 : ℂ)⁻¹ = 1 := by norm_num
  rw [← Complex.cpow_nat_mul, hExp, Complex.cpow_one]

private theorem complex_sqrt_ne_zero {w : ℂ} (hw : w ≠ 0) : Complex.sqrt w ≠ 0 := by
  intro h
  apply hw
  rw [← complex_sqrt_sq w, h, zero_pow (by decide : (2 : ℕ) ≠ 0)]

private def etaRootRatio (g : SL(2, ℤ)) (z : ℍ) : ℂ :=
  ModularForm.eta (g • z : ℍ) / (Complex.sqrt (denominator g z) * ModularForm.eta z)

private theorem etaRootRatio_sq (g : SL(2, ℤ)) (z : ℍ) :
    etaRootRatio g z ^ 2 = squaredMultiplier g := by
  rw [etaRootRatio, div_pow, mul_pow, eta_squared_transform, complex_sqrt_sq]
  exact mul_div_cancel_right₀ _ (mul_ne_zero (denominator_ne_zero g z)
    (pow_ne_zero _ (ModularForm.eta_ne_zero z.im_pos)))

private theorem etaRootRatio_continuous (g : SL(2, ℤ)) (hg : 0 < g 1 0) :
    Continuous (etaRootRatio g) := by
  have hEta := Paper8EtaRigidity.eta_holomorphic.continuous
  have hAct : Continuous (fun z : ℍ => g • z) := by
    simpa only [ModularGroup.sl_moeb] using
      (continuous_const_smul (g : GL (Fin 2) ℝ))
  have hD : Continuous (fun z : ℍ => denominator g z) := by
    unfold denominator
    fun_prop
  have hSqrt : Continuous (fun z : ℍ => Complex.sqrt (denominator g z)) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    have hPos : 0 < (denominator g z).im := by
      have hc : (0 : ℝ) < g 1 0 := by exact_mod_cast hg
      simpa [denominator, Complex.mul_im] using mul_pos hc z.im_pos
    change ContinuousAt (Complex.sqrt ∘ (fun w : ℍ => denominator g w)) z
    exact (Complex.continuousAt_sqrt (Or.inr hPos.ne')).comp hD.continuousAt
  exact (hEta.comp hAct).div (hSqrt.mul hEta) (fun z =>
    mul_ne_zero (complex_sqrt_ne_zero (denominator_ne_zero g z)) (ModularForm.eta_ne_zero z.im_pos))

private def basePoint : ℍ := ⟨Complex.I, by simp⟩

def principalEtaMultiplier (g : SL(2, ℤ)) : ℂ := etaRootRatio g basePoint

theorem principalEtaMultiplier_sq (g : SL(2, ℤ)) :
    principalEtaMultiplier g ^ 2 = squaredMultiplier g :=
  etaRootRatio_sq g basePoint

theorem principalEtaMultiplier_pow_twentyFour (g : SL(2, ℤ)) :
    principalEtaMultiplier g ^ 24 = 1 := by
  change principalEtaMultiplier g ^ (2 * 12) = 1
  rw [pow_mul, principalEtaMultiplier_sq, squaredMultiplier_pow_twelve]

theorem eta_principal_transform (g : SL(2, ℤ)) (hg : 0 < g 1 0) (z : ℍ) :
    ModularForm.eta (g • z : ℍ) =
      principalEtaMultiplier g * (Complex.sqrt (denominator g z) * ModularForm.eta z) := by
  let p : Polynomial ℂ := Polynomial.X ^ (2 : ℕ) - Polynomial.C (squaredMultiplier g)
  have hp : p ≠ 0 := by
    intro he
    have h := congrArg (fun q : Polynomial ℂ => q.coeff 2) he
    norm_num [p, Polynomial.coeff_X_pow, Polynomial.coeff_C] at h
  have hFin : (Set.range (etaRootRatio g)).Finite := by
    refine (Polynomial.finite_setOf_isRoot hp).subset ?_
    rintro _ ⟨w, rfl⟩
    change p.IsRoot (etaRootRatio g w)
    simp [p, Polynomial.IsRoot, etaRootRatio_sq]
  have hConn := isPreconnected_range (etaRootRatio_continuous g hg)
  have hSub : (Set.range (etaRootRatio g)).Subsingleton := by
    by_contra h
    exact hFin.not_infinite (hConn.infinite_of_nontrivial (not_subsingleton_iff.mp h))
  apply (div_eq_iff (mul_ne_zero (complex_sqrt_ne_zero (denominator_ne_zero g z))
    (ModularForm.eta_ne_zero z.im_pos))).mp
  exact hSub (Set.mem_range_self z) (Set.mem_range_self basePoint)

private def referencePoint (g : SL(2, ℤ)) (hg : 0 < g 1 0) : ℍ :=
  ⟨((-(g 1 1 : ℝ) / (g 1 0 : ℝ) : ℝ) : ℂ) +
      (((1 / (g 1 0 : ℝ)) : ℝ) : ℂ) * Complex.I, by
    have h : (0 : ℝ) < (g 1 0 : ℝ) := by exact_mod_cast hg
    simpa [Complex.mul_im] using one_div_pos.mpr h⟩

private theorem referencePoint_coe (g : SL(2, ℤ)) (hg : 0 < g 1 0) :
    (referencePoint g hg : ℂ) = (-(g 1 1 : ℂ) + Complex.I) / (g 1 0 : ℂ) := by
  change (((-(g 1 1 : ℝ) / (g 1 0 : ℝ) : ℝ) : ℂ) +
      (((1 / (g 1 0 : ℝ)) : ℝ) : ℂ) * Complex.I) = _
  push_cast
  ring

private theorem denominator_referencePoint (g : SL(2, ℤ)) (hg : 0 < g 1 0) :
    denominator g (referencePoint g hg) = Complex.I := by
  have hc : (g 1 0 : ℂ) ≠ 0 := by exact_mod_cast hg.ne'
  rw [denominator, referencePoint_coe]
  field_simp [hc] <;> ring

private theorem referencePoint_smul (g : SL(2, ℤ)) (hg : 0 < g 1 0) :
    ((g • referencePoint g hg : ℍ) : ℂ) = ((g 0 0 : ℂ) + Complex.I) / (g 1 0 : ℂ) := by
  have hc : (g 1 0 : ℂ) ≠ 0 := by exact_mod_cast hg.ne'
  have hdZ : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have h := g.2
    change Matrix.det g.1 = (1 : ℤ) at h
    rwa [Matrix.det_fin_two] at h
  have hd : (g 0 0 : ℂ) * (g 1 1 : ℂ) - (g 0 1 : ℂ) * (g 1 0 : ℂ) = 1 := by
    exact_mod_cast hdZ
  rw [← fractionalLinear_eq, fractionalLinear, denominator_referencePoint, referencePoint_coe]
  have hNum : (g 0 0 : ℂ) * ((-(g 1 1 : ℂ) + Complex.I) / (g 1 0 : ℂ)) + (g 0 1 : ℂ) =
      (-1 + (g 0 0 : ℂ) * Complex.I) / (g 1 0 : ℂ) := by
    apply (eq_div_iff hc).2
    rw [add_mul, mul_assoc, div_mul_cancel₀ _ hc]
    linear_combination -hd
  rw [hNum]
  apply (div_eq_iff Complex.I_ne_zero).2
  calc
    _ = (((g 0 0 : ℂ) + Complex.I) * Complex.I) / (g 1 0 : ℂ) := by
      congr 1
      linear_combination -Complex.I_sq
    _ = _ := by ring

theorem principalEtaMultiplier_at_reference_points (g : SL(2, ℤ)) (hg : 0 < g 1 0) :
    principalEtaMultiplier g =
      ModularForm.eta (((g 0 0 : ℂ) + Complex.I) / (g 1 0 : ℂ)) /
        (Complex.sqrt Complex.I *
          ModularForm.eta ((-(g 1 1 : ℂ) + Complex.I) / (g 1 0 : ℂ))) := by
  have h := eta_principal_transform g hg (referencePoint g hg)
  rw [referencePoint_smul, denominator_referencePoint] at h
  rw [← referencePoint_coe g hg]
  exact (eq_div_iff (mul_ne_zero (complex_sqrt_ne_zero Complex.I_ne_zero)
    (ModularForm.eta_ne_zero (referencePoint g hg).im_pos))).2 h.symm

end
end ManuscriptAudit.Paper8EtaPositiveLowerLeftMultiplier

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8EtaPositiveLowerLeftMultiplier.principalEtaMultiplier_sq,
      ``ManuscriptAudit.Paper8EtaPositiveLowerLeftMultiplier.principalEtaMultiplier_pow_twentyFour,
      ``ManuscriptAudit.Paper8EtaPositiveLowerLeftMultiplier.eta_principal_transform,
      ``ManuscriptAudit.Paper8EtaPositiveLowerLeftMultiplier.principalEtaMultiplier_at_reference_points] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
