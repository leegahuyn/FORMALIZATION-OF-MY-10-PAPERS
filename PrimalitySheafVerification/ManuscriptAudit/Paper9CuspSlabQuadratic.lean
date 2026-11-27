import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.GammaTwoQuotientHeightIntegral
import PrimalitySheafVerification.ManuscriptAudit.Paper9CuspLogMass
import PrimalitySheafVerification.ManuscriptAudit.Paper9LogQuadratic

/-! The native quotient pairing of a zero-mode profile on a finite cusp slab. -/

namespace ManuscriptAudit.Paper9CuspSlabQuadratic

open Set MeasureTheory
open GammaTwoQuotientHeightIntegral Paper9EisensteinHeightEquation
open Paper9CuspLogTransform Paper9CuspLogMass Paper9LogQuadratic
open Paper9HighCuspSection Paper9HighCuspCoordinates Paper9PrintedLaplacianSign
open Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry
open scoped UpperHalfPlane ComplexConjugate

noncomputable section

private theorem weighted_pair (g h : ℝ → ℂ) {y : ℝ} (hy : 0 < y) :
    (star (weightedLogProfile g y) * weightedLogProfile h y).re =
      y * (star (g (Real.log y)) * h (Real.log y)).re := by
  let c := heightPower (1 / 2 : ℂ) y
  have hc : star c * c = (y : ℂ) := by
    apply Complex.ext
    · rw [re_star_mul_self, Complex.ofReal_re]
      have h := critical_height_norm_sq 0 hy
      have he : criticalExponent 0 = (1 / 2 : ℂ) := by simp [criticalExponent]
      rwa [he] at h
    · change (conj c * c).im = _
      simp [Complex.mul_im] <;> ring
  change (star (c * g (Real.log y)) * (c * h (Real.log y))).re = _
  rw [star_mul]
  have he : star (g (Real.log y)) * star c * (c * h (Real.log y)) =
      (star c * c) * (star (g (Real.log y)) * h (Real.log y)) := by ring
  rw [he, hc, re_ofReal_mul]

def heightDensity (g g'' : ℝ → ℂ) (a b : ℝ) (y : ℝ) : ℝ :=
  (Ioc a b).indicator (fun y => modeDensity g g'' (Real.log y) * y⁻¹) y

def quotientDensity (g g'' : ℝ → ℂ) (a b : ℝ) (q : GammaTwoQuotient) : ℝ :=
  quotientHeight q ^ 2 * heightDensity g g'' a b (quotientHeight q)

theorem quotientDensity_on_slab (g : ℝ → ℂ)
    (hg : Differentiable ℝ g) (hg' : Differentiable ℝ (deriv g))
    {a b : ℝ} (ha : 1 < a) (z : ℍ) (hz : z.im ∈ Ioc a b) :
    quotientDensity g (deriv (deriv g)) a b (gammaTwoQuotientMk z) =
      (star (extendedSection (weightedLogProfile g) z) *
        printedL (coordinates (weightedLogProfile g)) z).re := by
  have hz' : 1 < z.im := ha.trans hz.1
  rw [quotientDensity, quotientHeight_high z hz'.le, heightDensity, indicator_of_mem hz,
    printedL_weightedLogProfile g hg hg' z hz', extendedSection_at_high _ z hz',
    weighted_pair g _ z.im_pos]
  change z.im ^ 2 * (modeDensity g (deriv (deriv g)) (Real.log z.im) * z.im⁻¹) =
    z.im * modeDensity g (deriv (deriv g)) (Real.log z.im)
  generalize modeDensity g (deriv (deriv g)) (Real.log z.im) = v
  field_simp [z.im_ne_zero] <;> ring

theorem quotient_form_eq (D : GammaTwoFundamentalDomain)
    (g g' g'' : ℝ → ℂ) {a b : ℝ} (ha : 1 < a) (hab : a ≤ b)
    (hg : ∀ t, HasDerivAt g (g' t) t) (hg' : ∀ t, HasDerivAt g' (g'' t) t)
    (hg'' : Continuous g'') (hga : g (Real.log a) = 0) (hgb : g (Real.log b) = 0) :
    (∫ q, quotientDensity g g'' a b q ∂D.quotientMeasure) =
      2 * (-(∫ t in Real.log a..Real.log b, ‖g' t‖ ^ (2 : ℕ)) -
        (1 / 4 : ℝ) * ∫ t in Real.log a..Real.log b, ‖g t‖ ^ (2 : ℕ)) := by
  have hG : Continuous g := continuous_iff_continuousAt.mpr (fun t => (hg t).continuousAt)
  have hCG : Continuous (fun t => star (g t)) := Complex.conjCLE.continuous.comp hG
  have hMode : Continuous (modeDensity g g'') :=
    Complex.continuous_re.comp (hCG.mul (hg''.sub (continuous_const.mul hG)))
  have hMeas : Measurable (heightDensity g g'' a b) :=
    ((hMode.measurable.comp Real.measurable_log).mul measurable_inv).indicator measurableSet_Ioc
  have hZero (y : ℝ) (hy : y ≤ 1) : heightDensity g g'' a b y = 0 :=
    indicator_of_notMem (fun h : y ∈ Ioc a b => (not_lt_of_ge (hy.trans ha.le)) h.1) _
  have hInterval :
      (∫ y in Ioi (1 : ℝ), heightDensity g g'' a b y) =
        ∫ y in a..b, modeDensity g g'' (Real.log y) * y⁻¹ := by
    rw [intervalIntegral.integral_of_le hab, ← integral_indicator measurableSet_Ioc,
      ← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro y
    by_cases hy : y ∈ Ioi (1 : ℝ)
    · rw [indicator_of_mem hy] <;> rfl
    · rw [indicator_of_notMem hy,
        indicator_of_notMem (fun h : y ∈ Ioc a b => hy (ha.trans h.1))]
  unfold quotientDensity
  rw [integral_profile D _ hMeas hZero, hInterval,
    log_substitution (modeDensity g g'') hMode (zero_lt_one.trans ha) hab,
    mode_form_eq g g' g'' _ _ hg hg' hg'' hga hgb]

end
end ManuscriptAudit.Paper9CuspSlabQuadratic

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper9CuspSlabQuadratic.quotientDensity_on_slab,
      ``ManuscriptAudit.Paper9CuspSlabQuadratic.quotient_form_eq] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
