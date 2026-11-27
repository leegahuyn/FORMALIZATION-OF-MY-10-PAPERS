import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaRigidity
import PrimalitySheafVerification.ManuscriptAudit.Paper8ActualEtaTranslation

/-! A holomorphic eta-normalized cusp translate with the true half-weight magnitude. -/

namespace ManuscriptAudit.Paper8EtaNormalizedCuspTranslate

open Set Function UpperHalfPlane
open Paper8EtaRigidity Paper8ActualEtaSquaredModularity Paper8EtaRatioCuspLimit
open scoped MatrixGroups Manifold

noncomputable section

def etaRatio (f : ℍ → ℂ) (z : ℍ) : ℂ := f z / ModularForm.eta z

def cuspTranslate (f : ℍ → ℂ) (g : SL(2, ℤ)) (z : ℂ) : ℂ :=
  etaRatio f (g • ofComplex z) * ModularForm.eta (ofComplex z : ℍ)

theorem etaRatio_holomorphic {f : ℍ → ℂ} (hHol : MDiff f) : MDiff (etaRatio f) := by
  simpa only [etaRatio, Pi.div_def] using hHol.div eta_holomorphic (fun z : ℍ =>
    ModularForm.eta_ne_zero z.im_pos)

theorem etaRatio_invariant {H : Subgroup SL(2, ℤ)} {f : ℍ → ℂ}
    (hAgree : ∀ g : SL(2, ℤ), g ∈ H → ∀ z : ℍ,
      f (g • z) * ModularForm.eta z = f z * ModularForm.eta (g • z : ℍ)) :
    ∀ g : SL(2, ℤ), g ∈ H → ∀ z : ℍ, etaRatio f (g • z) = etaRatio f z := by
  intro g hg z
  exact (div_eq_div_iff (ModularForm.eta_ne_zero (g • z : ℍ).im_pos)
    (ModularForm.eta_ne_zero z.im_pos)).2 (hAgree g hg z)

theorem cuspTranslate_holomorphic {f : ℍ → ℂ} (hHol : MDiff f) (g : SL(2, ℤ)) :
    DifferentiableOn ℂ (cuspTranslate f g) {z : ℂ | 0 < z.im} := by
  have h := (translate_holomorphic (etaRatio_holomorphic hHol) g).mul eta_holomorphic
  have hC := UpperHalfPlane.mdifferentiable_iff.mp h
  simpa only [Function.comp_apply, Pi.mul_def, cuspTranslate] using hC

theorem norm_cuspTranslate (f : ℍ → ℂ) (g : SL(2, ℤ)) (z : ℍ) :
    ‖cuspTranslate f g z‖ = ‖f (g • z)‖ / Real.sqrt ‖denominator g z‖ := by
  have hD : 0 < Real.sqrt ‖denominator g z‖ :=
    Real.sqrt_pos.2 (norm_pos_iff.mpr (denominator_ne_zero g z))
  have hEta : 0 < ‖ModularForm.eta z‖ := norm_pos_iff.mpr (ModularForm.eta_ne_zero z.im_pos)
  rw [cuspTranslate, ofComplex_apply, etaRatio, norm_mul, norm_div, eta_norm_transform]
  field_simp [hD.ne', hEta.ne'] <;> ring

private theorem eta_norm_add_nat (z : ℂ) (m : ℕ) :
    ‖ModularForm.eta (z + ((m : ℝ) : ℂ))‖ = ‖ModularForm.eta z‖ := by
  have h := Paper8ActualEtaTranslation.eta_add_integer z (m : ℤ)
  have hCast : ((m : ℤ) : ℂ) = ((m : ℝ) : ℂ) := by push_cast
  rw [hCast] at h
  rw [h, norm_mul, Complex.norm_exp]
  have hRe : (2 * (Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ) / (24 : ℂ)).re = 0 := by
    norm_num [Complex.div_re, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  rw [hRe, Real.exp_zero, one_mul]

theorem cuspTranslate_norm_sq_periodic {H : Subgroup SL(2, ℤ)} {f : ℍ → ℂ}
    (hAgree : ∀ g : SL(2, ℤ), g ∈ H → ∀ z : ℍ,
      f (g • z) * ModularForm.eta z = f z * ModularForm.eta (g • z : ℍ))
    (g : SL(2, ℤ)) {w : ℕ} (hMem : g * ModularGroup.T ^ (w : ℤ) * g⁻¹ ∈ H)
    (y : ℝ) (hy : 0 < y) :
    Periodic (fun x : ℝ => ‖cuspTranslate f g ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2) (w : ℝ) := by
  intro x
  let v (t : ℝ) : ℂ := (t : ℂ) + (y : ℂ) * Complex.I
  have hAdd : v (x + (w : ℝ)) = v x + ((w : ℝ) : ℂ) := by
    simp only [v, Complex.ofReal_add]
    ring
  have hz : 0 < (v x).im := by simpa [v, Complex.mul_im] using hy
  have hz' : 0 < (v x + ((w : ℝ) : ℂ)).im := by simpa using hz
  have hEta : ‖ModularForm.eta (ofComplex (v x + ((w : ℝ) : ℂ)) : ℍ)‖ =
      ‖ModularForm.eta (ofComplex (v x) : ℍ)‖ := by
    rw [ofComplex_apply_of_im_pos hz', ofComplex_apply_of_im_pos hz]
    exact eta_norm_add_nat (v x) w
  have hPer := translate_periodic_of_conjugatedTranslation_mem (etaRatio_invariant hAgree) g hMem (v x)
  change etaRatio f (g • ofComplex (v x + ((w : ℝ) : ℂ))) =
    etaRatio f (g • ofComplex (v x)) at hPer
  change ‖cuspTranslate f g (v (x + w))‖ ^ 2 = ‖cuspTranslate f g (v x)‖ ^ 2
  simp only [hAdd, cuspTranslate, norm_mul, hPer, hEta]

end
end ManuscriptAudit.Paper8EtaNormalizedCuspTranslate

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8EtaNormalizedCuspTranslate.etaRatio_holomorphic,
      ``ManuscriptAudit.Paper8EtaNormalizedCuspTranslate.etaRatio_invariant,
      ``ManuscriptAudit.Paper8EtaNormalizedCuspTranslate.cuspTranslate_holomorphic,
      ``ManuscriptAudit.Paper8EtaNormalizedCuspTranslate.norm_cuspTranslate,
      ``ManuscriptAudit.Paper8EtaNormalizedCuspTranslate.cuspTranslate_norm_sq_periodic] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
