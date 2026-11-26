import Lean.Util.CollectAxioms
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import PrimalitySheafVerification.ManuscriptAudit.HighInfinityCusp
import PrimalitySheafVerification.ManuscriptAudit.Paper10CoulombProductRule

/-!
# A nonzero derivative test in the actual infinity cusp

The test uses the unprojected covariant-derivative convention of
Remark 4.12 at zero background. Its support is in the interior of the
width-two cusp cylinder truncated at height six. The coordinate
calculation uses the hyperbolic metric and its genuine conformal
Christoffel coefficient.
-/

namespace ManuscriptAudit.HyperbolicCuspGaugeTest

open MeasureTheory Paper10CoulombMultiplier Paper10CoulombProductRule
open LiteralCuspTruncation (orbitPoint)
open scoped UpperHalfPlane

noncomputable section

def cuspBump (y : ℝ) : ℝ :=
  Real.smoothTransition (y - 2) * Real.smoothTransition (5 - y)

theorem cuspBump_smooth : ContDiff ℝ (↑(⊤ : WithTop ℕ)) cuspBump := by
  have hLeft : ContDiff ℝ (↑(⊤ : WithTop ℕ)) (fun y : ℝ => y - 2) :=
    contDiff_id.sub contDiff_const
  have hRight : ContDiff ℝ (↑(⊤ : WithTop ℕ)) (fun y : ℝ => 5 - y) :=
    contDiff_const.sub contDiff_id
  exact (Real.smoothTransition.contDiff.comp hLeft).mul (Real.smoothTransition.contDiff.comp hRight)

theorem cuspBump_zero_of_height_outside {y : ℝ} (h : y ≤ 2 ∨ 5 ≤ y) :
    cuspBump y = 0 := by
  rcases h with h | h
  · rw [cuspBump, Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr h), zero_mul]
  · rw [cuspBump, Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr h), mul_zero]

theorem cuspBump_one_on_middle {y : ℝ} (h₁ : 3 ≤ y) (h₂ : y ≤ 4) :
    cuspBump y = 1 := by
  rw [cuspBump, Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ y - 2),
    Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 5 - y), one_mul]

def cuspOneForm : OneForm := fun _ y => (cuspBump y, 0)

theorem cuspOneForm_coclosed (x y : ℝ) : codifferential cuspOneForm x y = 0 := by
  rw [codifferential_eq_coordinateDivergence]
  simp [cuspOneForm]

theorem cuspOneForm_same_on_high_orbit {z w : ℍ} (hz : 1 < z.im) (hw : 1 < w.im)
    (h : orbitPoint w = orbitPoint z) :
    cuspOneForm w.re w.im = cuspOneForm z.re z.im := by
  obtain ⟨m, hm⟩ :=
    (HighInfinityCusp.high_orbitPoint_eq_iff_even_translate le_rfl hz hw).mp h
  have him := congrArg Complex.im hm
  have hHeight : w.im = z.im := by
    simpa [Complex.add_im, Complex.mul_im] using him
  simp only [cuspOneForm, hHeight]

/-- This is Gamma^x_xy = Gamma^x_yx for the metric y⁻²(dx² + dy²). -/
def christoffel_xy_x (y : ℝ) : ℝ :=
  (1 / 2) * y ^ 2 * deriv (fun t : ℝ => (t ^ 2)⁻¹) y

theorem christoffel_xy_x_eq {y : ℝ} (hy : 0 < y) : christoffel_xy_x y = -1 / y := by
  have h := ((hasDerivAt_id y).pow 2).inv (pow_ne_zero 2 hy.ne')
  have h' : HasDerivAt (fun t : ℝ => (t ^ 2)⁻¹) (-(2 * y) / (y ^ 2) ^ 2) y := by
    convert h using 1 <;> norm_num [id]
  rw [christoffel_xy_x, h'.deriv]
  field_simp [hy.ne'] <;> ring

/-- For this horizontal one-form, these are the xy and yx components of ∇a. -/
def cuspCovariantComponents (y : ℝ) : ℝ × ℝ :=
  (-(christoffel_xy_x y) * cuspBump y, deriv cuspBump y - christoffel_xy_x y * cuspBump y)

theorem cuspCovariantComponents_norm_density {y : ℝ} (hy : 0 < y) :
    y ^ 2 * ((cuspCovariantComponents y).1 ^ 2 + (cuspCovariantComponents y).2 ^ 2) =
      cuspBump y ^ 2 + (y * deriv cuspBump y + cuspBump y) ^ 2 := by
  rw [cuspCovariantComponents, christoffel_xy_x_eq hy]
  dsimp
  field_simp [hy.ne'] <;> ring

def cuspMass : ℝ := 2 * ∫ y : ℝ in (1 : ℝ)..6, cuspBump y ^ 2

def cuspDerivativeEnergy : ℝ :=
  2 * ∫ y : ℝ in (1 : ℝ)..6, cuspBump y ^ 2 + (y * deriv cuspBump y + cuspBump y) ^ 2

theorem cuspMass_pos : 0 < cuspMass := by
  unfold cuspMass
  apply mul_pos (by norm_num)
  apply intervalIntegral.integral_pos (by norm_num : (1 : ℝ) < 6)
    (cuspBump_smooth.continuous.pow 2).continuousOn
  · intro y _
    exact sq_nonneg _
  · refine ⟨7 / 2, by constructor <;> norm_num, ?_⟩
    change 0 < cuspBump (7 / 2) ^ (2 : ℕ)
    rw [cuspBump_one_on_middle (y := 7 / 2) (by norm_num) (by norm_num)]
    norm_num

theorem cuspMass_le_cuspDerivativeEnergy : cuspMass ≤ cuspDerivativeEnergy := by
  have hB := cuspBump_smooth.continuous
  have hD := cuspBump_smooth.continuous_deriv (by simp)
  have hM : Continuous (fun y : ℝ => cuspBump y ^ 2) := hB.pow 2
  have hE : Continuous (fun y : ℝ => (y * deriv cuspBump y + cuspBump y) ^ 2) :=
    ((continuous_id.mul hD).add hB).pow 2
  unfold cuspMass cuspDerivativeEnergy
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact intervalIntegral.integral_mono (by norm_num : (1 : ℝ) ≤ 6)
    (hM.intervalIntegrable 1 6) ((hM.add hE).intervalIntegrable 1 6)
    (fun y => le_add_of_nonneg_right (sq_nonneg _))

theorem negative_zero_potential_form : -cuspDerivativeEnergy < 0 :=
  neg_lt_zero.mpr (cuspMass_pos.trans_le cuspMass_le_cuspDerivativeEnergy)

theorem opposite_printed_forms_disagree (potentialContribution : ℝ) :
    -cuspDerivativeEnergy + potentialContribution ≠
      cuspDerivativeEnergy + potentialContribution := by
  have h := cuspMass_pos.trans_le cuspMass_le_cuspDerivativeEnergy
  intro hEq
  linarith

end
end ManuscriptAudit.HyperbolicCuspGaugeTest

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.HyperbolicCuspGaugeTest.cuspBump_smooth,
      ``ManuscriptAudit.HyperbolicCuspGaugeTest.cuspBump_zero_of_height_outside,
      ``ManuscriptAudit.HyperbolicCuspGaugeTest.cuspOneForm_coclosed,
      ``ManuscriptAudit.HyperbolicCuspGaugeTest.cuspOneForm_same_on_high_orbit,
      ``ManuscriptAudit.HyperbolicCuspGaugeTest.christoffel_xy_x_eq,
      ``ManuscriptAudit.HyperbolicCuspGaugeTest.cuspCovariantComponents_norm_density,
      ``ManuscriptAudit.HyperbolicCuspGaugeTest.cuspMass_pos,
      ``ManuscriptAudit.HyperbolicCuspGaugeTest.cuspMass_le_cuspDerivativeEnergy,
      ``ManuscriptAudit.HyperbolicCuspGaugeTest.negative_zero_potential_form,
      ``ManuscriptAudit.HyperbolicCuspGaugeTest.opposite_printed_forms_disagree] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
