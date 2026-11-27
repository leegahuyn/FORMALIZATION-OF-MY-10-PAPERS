import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper9CuspLaplacianTest
import PrimalitySheafVerification.ManuscriptAudit.Paper9CuspPotentialForm
import PrimalitySheafVerification.ManuscriptAudit.Paper9HighCuspCoordinates

/-! The printed negative Laplacian has negative quadratic density on an actual compact cusp section. -/

namespace ManuscriptAudit.Paper9HighCuspNegative

open Filter MeasureTheory Set MaassLaplacian HyperbolicCuspGaugeTest
open Paper9HighCuspSection Paper9HighCuspCoordinates Paper9PrintedLaplacianSign Paper9CuspPotentialForm
open scoped UpperHalfPlane ContDiff

noncomputable section

def heightAmplitude (Y y : ℝ) : ℂ := (heightTest Y y : ℂ)

theorem heightAmplitude_smooth (Y : ℝ) : ContDiff ℝ ∞ (heightAmplitude Y) :=
  Complex.ofRealCLM.contDiff.comp (heightTest_smooth Y)

theorem heightAmplitude_zero (Y y : ℝ) (h : y < Y + 2 ∨ Y + 5 < y) :
    heightAmplitude Y y = 0 := by
  unfold heightAmplitude
  rw [heightTest_zero Y y (h.imp le_of_lt le_of_lt), Complex.ofReal_zero]

private theorem bump_differentiable : Differentiable ℝ cuspBump :=
  (contDiff_infty.mp cuspBump_smooth 1).differentiable (by decide)

private theorem bump_deriv_differentiable : Differentiable ℝ (deriv cuspBump) := by
  have hs : ContDiff ℝ (1 + 1) cuspBump := contDiff_infty.mp cuspBump_smooth 2
  exact hs.deriv'.differentiable (by decide)

theorem heightAmplitude_deriv (Y y : ℝ) :
    deriv (heightAmplitude Y) y = ((deriv cuspBump (y - Y) : ℝ) : ℂ) := by
  have h := ((bump_differentiable (y - Y)).hasDerivAt.comp y
    ((hasDerivAt_id y).sub_const Y)).ofReal_comp
  simpa [Function.comp_def, heightAmplitude, heightTest] using h.deriv

theorem heightAmplitude_second (Y y : ℝ) :
    deriv (deriv (heightAmplitude Y)) y = ((deriv (deriv cuspBump) (y - Y) : ℝ) : ℂ) := by
  rw [funext (heightAmplitude_deriv Y)]
  have h := ((bump_deriv_differentiable (y - Y)).hasDerivAt.comp y
    ((hasDerivAt_id y).sub_const Y)).ofReal_comp
  simpa [Function.comp_def] using h.deriv

def quadraticDensity (Y : ℝ) (z : ℍ) : ℝ :=
  (printedL (coordinates (heightAmplitude Y)) z *
    (starRingEnd ℂ) (extendedSection (heightAmplitude Y) z)).re / z.im ^ 2

theorem quadraticDensity_high (Y : ℝ) (z : ℍ) (hz : 1 < z.im) :
    quadraticDensity Y z = deriv (deriv cuspBump) (z.im - Y) * cuspBump (z.im - Y) := by
  rw [quadraticDensity, printedL_high _ z hz, heightAmplitude_second,
    extendedSection_at_high _ z hz, heightAmplitude, heightTest]
  simp only [Complex.conj_ofReal, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  field_simp [z.im_ne_zero]

private def stripPoint (x t : ℝ) : ℍ :=
  UpperHalfPlane.ofComplex (complexPoint x (1 + t))

private theorem stripPoint_height (x t : ℝ) (ht : 1 ≤ t) :
    (stripPoint x t).im = 1 + t := by
  have hpos : 0 < (complexPoint x (1 + t)).im := by rw [complexPoint_im]; linarith
  unfold stripPoint
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hpos]
  exact complexPoint_im _ _

theorem actual_compact_cusp_test_negative (x : ℝ) :
    HasCompactSupport (quotientProfile (heightAmplitude 1)) ∧
      2 * (∫ t : ℝ in (1 : ℝ)..6, quadraticDensity 1 (stripPoint x t)) < 0 := by
  refine ⟨profile_hasCompactSupport _ 1 le_rfl (heightAmplitude_zero 1), ?_⟩
  have he : (∫ t : ℝ in (1 : ℝ)..6, quadraticDensity 1 (stripPoint x t)) =
      ∫ t : ℝ in (1 : ℝ)..6, deriv (deriv cuspBump) t * cuspBump t := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 6)]
    intro t ht
    have him := stripPoint_height x t ht.1
    have hhigh : 1 < (stripPoint x t).im := by rw [him]; linarith [ht.1]
    have hsub : 1 + t - 1 = t := by ring
    change quadraticDensity 1 (stripPoint x t) = deriv (deriv cuspBump) t * cuspBump t
    rw [quadraticDensity_high _ _ hhigh, him, hsub]
  rw [he]
  exact Paper9CuspLaplacianTest.compact_cusp_test_negative

end
end ManuscriptAudit.Paper9HighCuspNegative

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper9HighCuspNegative.heightAmplitude_smooth,
      ``ManuscriptAudit.Paper9HighCuspNegative.heightAmplitude_deriv,
      ``ManuscriptAudit.Paper9HighCuspNegative.heightAmplitude_second,
      ``ManuscriptAudit.Paper9HighCuspNegative.quadraticDensity_high,
      ``ManuscriptAudit.Paper9HighCuspNegative.actual_compact_cusp_test_negative] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
