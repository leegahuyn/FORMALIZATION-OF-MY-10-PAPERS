import Lean.Util.CollectAxioms
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import PrimalitySheafVerification.ManuscriptAudit.Paper8ModularHeightCutoff

/-! Smooth modular cutoffs with a uniform hyperbolic height-derivative bound. -/

namespace ManuscriptAudit.Paper8MaassCutoffTaper

open Set Filter UpperHalfPlane Paper8ModularHeightCutoff
open scoped MatrixGroups Topology

noncomputable section

def baseTaper (t : ℝ) : ℝ := 1 - Real.smoothTransition (t - 1)

private theorem baseTaper_smooth : ContDiff ℝ ∞ baseTaper := by
  unfold baseTaper
  exact contDiff_const.sub (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const))

theorem baseTaper_eq_one {t : ℝ} (ht : t ≤ 1) : baseTaper t = 1 := by
  rw [baseTaper, Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr ht), sub_zero]

theorem baseTaper_eq_zero {t : ℝ} (ht : 2 ≤ t) : baseTaper t = 0 := by
  rw [baseTaper, Real.smoothTransition.one_of_one_le (by linarith), sub_self]

private theorem baseTaper_deriv_zero {t : ℝ} (ht : t < 1 ∨ 2 < t) : deriv baseTaper t = 0 := by
  rcases ht with h | h
  · have hEq : baseTaper =ᶠ[𝓝 t] (fun _ : ℝ => (1 : ℝ)) :=
      (Iio_mem_nhds h).mono (fun _ hs => baseTaper_eq_one hs.le)
    rw [hEq.deriv_eq]
    simp
  · have hEq : baseTaper =ᶠ[𝓝 t] (fun _ : ℝ => (0 : ℝ)) :=
      (Ioi_mem_nhds h).mono (fun _ hs => baseTaper_eq_zero hs.le)
    rw [hEq.deriv_eq]
    simp

private theorem baseTaper_deriv_bounded :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, |deriv baseTaper t| ≤ C := by
  have hc : Continuous (fun t => |deriv baseTaper t|) :=
    (baseTaper_smooth.continuous_deriv (by norm_num)).abs
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := 2)).bddAbove_image hc.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun t => ?_⟩
  by_cases ht : t ∈ Icc (1 : ℝ) 2
  · exact (hM (mem_image_of_mem (fun u => |deriv baseTaper u|) ht)).trans (le_max_left _ _)
  · have hOut : t < 1 ∨ 2 < t := by
      by_contra! hn
      exact ht ⟨hn.1, hn.2⟩
    rw [baseTaper_deriv_zero hOut, abs_zero]
    exact le_max_right _ _

def taper (Y t : ℝ) : ℝ := baseTaper (t / Y)

theorem taper_smooth (Y : ℝ) : ContDiff ℝ ∞ (taper Y) := by
  unfold taper
  exact baseTaper_smooth.comp (by fun_prop : ContDiff ℝ ∞ (fun t : ℝ => t / Y))

theorem taper_eq_one {Y t : ℝ} (hY : 0 < Y) (ht : t ≤ Y) : taper Y t = 1 :=
  baseTaper_eq_one ((div_le_iff₀ hY).2 (by simpa only [one_mul] using ht))

theorem taper_eq_zero {Y t : ℝ} (hY : 0 < Y) (ht : 2 * Y ≤ t) : taper Y t = 0 :=
  baseTaper_eq_zero ((le_div_iff₀ hY).2 ht)

private theorem taper_deriv (Y t : ℝ) :
    deriv (taper Y) t = deriv baseTaper (t / Y) / Y := by
  have h := (baseTaper_smooth.differentiable (by norm_num) (t / Y)).hasDerivAt
  have hDiv : HasDerivAt (fun u : ℝ => u / Y) (1 / Y) t := by
    simpa only [id_eq] using (hasDerivAt_id t).div_const Y
  simpa only [taper, Function.comp_def, div_eq_mul_inv, one_mul] using (h.comp t hDiv).deriv

theorem height_deriv_taper_uniform :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y > 0, ∀ t : ℝ, |t * deriv (taper Y) t| ≤ C := by
  obtain ⟨C, hC, hBound⟩ := baseTaper_deriv_bounded
  refine ⟨2 * C, by positivity, fun Y _ t => ?_⟩
  rw [taper_deriv]
  by_cases ht : t / Y ∈ Icc (1 : ℝ) 2
  · have ht0 : 0 ≤ t / Y := zero_le_one.trans ht.1
    rw [show t * (deriv baseTaper (t / Y) / Y) =
      (t / Y) * deriv baseTaper (t / Y) by ring, abs_mul, abs_of_nonneg ht0]
    exact mul_le_mul ht.2 (hBound _) (abs_nonneg _) (by norm_num)
  · have hOut : t / Y < 1 ∨ 2 < t / Y := by
      by_contra! h
      exact ht ⟨h.1, h.2⟩
    rw [baseTaper_deriv_zero hOut, zero_div, mul_zero, abs_zero]
    positivity

def modularCutoff (Y : ℝ) (z : ℍ) : ℝ := taper Y (maximumHeight z)

theorem modularCutoff_invariant (Y : ℝ) (g : SL(2, ℤ)) (z : ℍ) :
    modularCutoff Y (g • z) = modularCutoff Y z := by
  simp only [modularCutoff, maximumHeight_invariant]

theorem modularCutoff_real_smooth {Y : ℝ} (hY : 2 < Y) :
    ContDiffOn ℝ ∞ (fun w : ℂ => modularCutoff Y (ofComplex w)) {w : ℂ | 0 < w.im} :=
  cutoff_real_smooth (taper Y) (taper_smooth Y) hY (fun _ => taper_eq_one (by linarith))

theorem modularCutoff_nonzero_reduced_to_truncation {Y : ℝ} (hY : 0 < Y) {z : ℍ}
    (hz : modularCutoff Y z ≠ 0) :
    ∃ g : SL(2, ℤ), g • z ∈ ModularGroup.truncatedFundamentalDomain (2 * Y) :=
  cutoff_nonzero_reduced_to_truncation (taper Y) (fun _ ht => taper_eq_zero hY ht.le) hz

end
end ManuscriptAudit.Paper8MaassCutoffTaper

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8MaassCutoffTaper.height_deriv_taper_uniform,
      ``ManuscriptAudit.Paper8MaassCutoffTaper.modularCutoff_invariant,
      ``ManuscriptAudit.Paper8MaassCutoffTaper.modularCutoff_real_smooth,
      ``ManuscriptAudit.Paper8MaassCutoffTaper.modularCutoff_nonzero_reduced_to_truncation] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
