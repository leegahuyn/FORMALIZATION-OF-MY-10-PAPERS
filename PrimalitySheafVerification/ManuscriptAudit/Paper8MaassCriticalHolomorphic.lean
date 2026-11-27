import Lean.Util.CollectAxioms
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import PrimalitySheafVerification.ManuscriptAudit.Paper8NegativeHalfMaassFactorization

/-!
# The negative half-weight raising kernel is conjugate holomorphic

Dividing a critical raising-kernel function by the positive quarter
power of height and conjugating gives a holomorphic function.
The proof uses real Fréchet differentiability and verifies the
Cauchy–Riemann equation for the two coordinate derivatives.
-/

namespace ManuscriptAudit.Paper8MaassCriticalHolomorphic

open MaassLaplacian Paper8NegativeHalfMaassFactorization

noncomputable section

def realProfile (F : ℂ → ℂ) (x y : ℝ) : ℂ := F (complexPoint x y)

def holomorphicPartner (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  (z.im ^ (-(1 / 4 : ℝ)) : ℝ) * (starRingEnd ℂ) (F z)

private theorem realEmbedding_derivative (r : ℝ) :
    HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) r := by
  simpa only [id_eq, Complex.ofReal_one] using (hasDerivAt_id r).ofReal_comp

private theorem point_horizontal (x y : ℝ) :
    HasDerivAt (fun t => complexPoint t y) (1 : ℂ) x :=
  (realEmbedding_derivative x).add_const ((y : ℂ) * Complex.I)

private theorem point_vertical (x y : ℝ) :
    HasDerivAt (fun t => complexPoint x t) Complex.I y := by
  simpa only [complexPoint, one_mul] using
    ((realEmbedding_derivative y).mul_const Complex.I).const_add (x : ℂ)

private theorem profile_horizontal {f : ℂ → ℂ} {x y : ℝ}
    (h : DifferentiableAt ℝ f (complexPoint x y)) :
    HasDerivAt (fun t => realProfile f t y) (partialX (realProfile f) x y) x := by
  have hd := h.hasFDerivAt.comp_hasDerivAt x (point_horizontal x y)
  exact hd.differentiableAt.hasDerivAt

private theorem profile_vertical {f : ℂ → ℂ} {x y : ℝ}
    (h : DifferentiableAt ℝ f (complexPoint x y)) :
    HasDerivAt (realProfile f x) (partialY (realProfile f) x y) y := by
  have hd := h.hasFDerivAt.comp_hasDerivAt y (point_vertical x y)
  exact hd.differentiableAt.hasDerivAt

private theorem differentiableAt_complex_of_coordinates {f : ℂ → ℂ} {x y : ℝ}
    (h : DifferentiableAt ℝ f (complexPoint x y))
    (hCR : partialY (realProfile f) x y = Complex.I * partialX (realProfile f) x y) :
    DifferentiableAt ℂ f (complexPoint x y) := by
  let L := fderiv ℝ f (complexPoint x y)
  have hdx : partialX (realProfile f) x y = L 1 :=
    (h.hasFDerivAt.comp_hasDerivAt x (point_horizontal x y)).deriv
  have hdy : partialY (realProfile f) x y = L Complex.I :=
    (h.hasFDerivAt.comp_hasDerivAt y (point_vertical x y)).deriv
  have hI : L Complex.I = Complex.I * L 1 := by
    rw [hdx, hdy] at hCR
    exact hCR
  apply (differentiableAt_iff_restrictScalars ℝ h).2
  refine ⟨(1 : ℂ →L[ℂ] ℂ).smulRight (L 1), ?_⟩
  apply ContinuousLinearMap.ext
  intro z
  change z * L 1 = L z
  have hz : z.re • (1 : ℂ) + z.im • Complex.I = z := by
    simpa only [Complex.real_smul, mul_one] using Complex.re_add_im z
  calc
    _ = (z.re • (1 : ℂ) + z.im • Complex.I) * L 1 := by rw [hz]
    _ = L (z.re • (1 : ℂ) + z.im • Complex.I) := by
      rw [map_add, map_smul, map_smul, hI]
      simp only [Complex.real_smul]
      ring
    _ = _ := by rw [hz]

private theorem conjugate_hasDerivAt {f : ℝ → ℂ} {d : ℂ} {x : ℝ} (h : HasDerivAt f d x) :
    HasDerivAt (fun t => (starRingEnd ℂ) (f t)) ((starRingEnd ℂ) d) x := by
  exact Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt x h

private theorem quarter_derivative {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => ((t ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ))
      ((-(1 / 4 : ℂ)) * ((y ^ (-(1 / 4 : ℝ) - 1) : ℝ) : ℂ)) y := by
  simpa only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat] using
    (Real.hasDerivAt_rpow_const (p := -(1 / 4 : ℝ)) (Or.inl hy.ne')).ofReal_comp

private theorem height_shift {y : ℝ} (hy : 0 < y) :
    (y : ℂ) * ((y ^ (-(1 / 4 : ℝ) - 1) : ℝ) : ℂ) =
      ((y ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) := by
  have hr := Real.rpow_add hy 1 (-(1 / 4 : ℝ) - 1)
  rw [show (1 : ℝ) + (-(1 / 4 : ℝ) - 1) = -(1 / 4 : ℝ) by ring, Real.rpow_one] at hr
  simpa only [Complex.ofReal_mul] using congrArg Complex.ofReal hr.symm

theorem partner_differentiableAt {F : ℂ → ℂ} {x y : ℝ} (hy : 0 < y)
    (hF : DifferentiableAt ℝ F (complexPoint x y))
    (hKernel : raising (realProfile F) x y = 0) :
    DifferentiableAt ℂ (holomorphicPartner F) (complexPoint x y) := by
  let A : ℂ := (y ^ (-(1 / 4 : ℝ)) : ℝ)
  let B : ℂ := (y ^ (-(1 / 4 : ℝ) - 1) : ℝ)
  let c : ℂ →+* ℂ := starRingEnd ℂ
  have hPow : DifferentiableAt ℝ
      (fun z : ℂ => ((z.im ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ)) (complexPoint x y) := by
    have h := (quarter_derivative hy).differentiableAt
    have hIm : DifferentiableAt ℝ (fun z : ℂ => z.im) (complexPoint x y) :=
      Complex.imCLM.differentiableAt
    have hh : DifferentiableAt ℝ (fun t : ℝ => ((t ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ))
          (complexPoint x y).im := by simpa only [complexPoint_im] using h
    exact hh.comp _ hIm
  have hPartnerReal : DifferentiableAt ℝ (holomorphicPartner F) (complexPoint x y) :=
    hPow.mul (Complex.differentiable_conj.differentiableAt.comp _ hF)
  apply differentiableAt_complex_of_coordinates hPartnerReal
  have hx := (conjugate_hasDerivAt (profile_horizontal hF)).const_mul A
  have hdx : partialX (realProfile (holomorphicPartner F)) x y =
      A * c (partialX (realProfile F) x y) := by
    simpa only [partialX, realProfile, holomorphicPartner, complexPoint_im, A, c] using hx.deriv
  have hv := (quarter_derivative hy).mul (conjugate_hasDerivAt (profile_vertical hF))
  have hdy : partialY (realProfile (holomorphicPartner F)) x y =
      (-(1 / 4 : ℂ)) * B * c (realProfile F x y) + A * c (partialY (realProfile F) x y) := by
    simpa only [Pi.mul_apply, partialY, realProfile, holomorphicPartner, complexPoint_im, A, B, c]
      using hv.deriv
  have hC : (-Complex.I) * (y : ℂ) * c (partialX (realProfile F) x y) +
      (y : ℂ) * c (partialY (realProfile F) x y) -
      (1 / 4 : ℂ) * c (realProfile F x y) = 0 := by
    have h := congrArg (starRingEnd ℂ) hKernel
    simpa only [raising, map_sub, map_add, map_mul, map_zero, map_div₀, map_one, map_ofNat,
      Complex.conj_I, Complex.conj_ofReal, c] using h
  have hShift : (y : ℂ) * B = A := height_shift hy
  rw [hdy, hdx]
  apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hy.ne')
  linear_combination A * hC - ((1 / 4 : ℂ) * c (realProfile F x y)) * hShift

theorem partner_differentiableOn {F : ℂ → ℂ}
    (hF : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℝ F z)
    (hKernel : ∀ x y : ℝ, 0 < y → raising (realProfile F) x y = 0) :
    DifferentiableOn ℂ (holomorphicPartner F) {z : ℂ | 0 < z.im} := by
  intro z hz
  have hPoint : complexPoint z.re z.im = z := Complex.re_add_im z
  have hDiff : DifferentiableAt ℝ F (complexPoint z.re z.im) := by rw [hPoint]; exact hF z hz
  have hHol := partner_differentiableAt hz hDiff (hKernel z.re z.im hz)
  rw [hPoint] at hHol
  exact hHol.differentiableWithinAt

end
end ManuscriptAudit.Paper8MaassCriticalHolomorphic

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8MaassCriticalHolomorphic.partner_differentiableAt,
      ``ManuscriptAudit.Paper8MaassCriticalHolomorphic.partner_differentiableOn] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
