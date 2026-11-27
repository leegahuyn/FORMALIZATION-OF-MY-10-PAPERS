import Lean.Util.CollectAxioms
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.NumberTheory.ModularForms.DedekindEta
import PrimalitySheafVerification.ManuscriptAudit.MaassLaplacian

/-! Conjugation of the Maass operator and the actual eta mode at weight −1/2. -/

namespace ManuscriptAudit.Paper8EtaNegativeHalfEigenmode

open MaassLaplacian

noncomputable section

def conjugate (F : ℝ → ℝ → ℂ) (x y : ℝ) : ℂ :=
  star (F x y)

private theorem derivative_conjugate (f : ℝ → ℂ) (x : ℝ) :
    deriv (fun t => star (f t)) x = star (deriv f x) := by
  by_cases hf : DifferentiableAt ℝ f x
  · exact ((Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt x hf.hasDerivAt).deriv
  · have hcf : ¬ DifferentiableAt ℝ (fun t => star (f t)) x := by
      intro h
      apply hf
      have h' := ((Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt
        x h.hasDerivAt).differentiableAt
      simpa only [star_star] using h'
    rw [deriv_zero_of_not_differentiableAt hcf, deriv_zero_of_not_differentiableAt hf, star_zero]

private theorem partialX_conjugate (F : ℝ → ℝ → ℂ) :
    partialX (conjugate F) = conjugate (partialX F) := by
  funext x y
  exact derivative_conjugate (fun t => F t y) x

private theorem partialY_conjugate (F : ℝ → ℝ → ℂ) :
    partialY (conjugate F) = conjugate (partialY F) := by
  funext x y
  exact derivative_conjugate (F x) y

theorem maass_conjugate (k : ℝ) (F : ℝ → ℝ → ℂ) (x y : ℝ) :
    maassDelta (-k) (conjugate F) x y = star (maassDelta k F x y) := by
  have hy : star (y : ℂ) = (y : ℂ) := Complex.conj_ofReal y
  have hk : star (k : ℂ) = (k : ℂ) := Complex.conj_ofReal k
  have hi : star Complex.I = -Complex.I := Complex.conj_I
  unfold maassDelta
  rw [partialX_conjugate F, partialY_conjugate F, partialX_conjugate (partialX F),
    partialY_conjugate (partialY F)]
  simp only [conjugate, Complex.ofReal_neg, star_add, star_mul, star_neg, star_pow, hy, hk, hi]
  ring

def etaNegativeHalf (x y : ℝ) : ℂ :=
  conjugate (weighted (1/4) ModularForm.eta) x y

theorem eta_negative_half_eigenvalue (x y : ℝ) (hy : 0 < y) :
    maassDelta (-1/2) etaNegativeHalf x y = (3/16 : ℂ) * etaNegativeHalf x y := by
  have h := delta_weighted ModularForm.eta (1/4) x y hy
    (fun _ hz => ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hz)
  have h' : maassDelta (1/2) (weighted (1/4) ModularForm.eta) x y =
      (3/16 : ℂ) * weighted (1/4) ModularForm.eta x y := by
    norm_num [Complex.ofReal_div] at h ⊢
    exact h
  have hc : star (3/16 : ℂ) = (3/16 : ℂ) := by
    change (starRingEnd ℂ) (3/16 : ℂ) = _
    simp [map_div₀]
  change maassDelta (-1/2) (conjugate (weighted (1/4) ModularForm.eta)) x y = _
  rw [show (-1/2 : ℝ) = -(1/2) by ring, maass_conjugate, h', star_mul, hc]
  unfold etaNegativeHalf conjugate
  ring

theorem eta_negative_half_ne_zero (x y : ℝ) (hy : 0 < y) :
    etaNegativeHalf x y ≠ 0 := by
  unfold etaNegativeHalf conjugate weighted
  have hW : (↑(y ^ (1/4 : ℝ)) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos hy (1/4 : ℝ)).ne'
  have hEta : ModularForm.eta (complexPoint x y) ≠ 0 := by
    apply ModularForm.eta_ne_zero
    change 0 < (complexPoint x y).im
    rwa [complexPoint_im]
  intro h
  apply mul_ne_zero hW hEta
  simpa only [star_star, star_zero] using congrArg star h

end
end ManuscriptAudit.Paper8EtaNegativeHalfEigenmode

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.Paper8EtaNegativeHalfEigenmode.maass_conjugate,
      ``ManuscriptAudit.Paper8EtaNegativeHalfEigenmode.eta_negative_half_eigenvalue,
      ``ManuscriptAudit.Paper8EtaNegativeHalfEigenmode.eta_negative_half_ne_zero] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
