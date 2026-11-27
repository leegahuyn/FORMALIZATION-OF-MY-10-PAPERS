import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.HyperbolicCuspGaugeTest

/-! Smooth co-closed one-forms supported in a fixed genuine high-cusp strip. -/

namespace ManuscriptAudit.CoulombScaledCuspForms

open HyperbolicCuspGaugeTest Paper10CoulombMultiplier Paper10CoulombProductRule
open LiteralCuspTruncation (orbitPoint)
open scoped UpperHalfPlane ContDiff

noncomputable section

def shift (r : ℝ) : ℝ := 2 - 2 * r

def scaleHeight (r y : ℝ) : ℝ := r * y + shift r

def amplitude (r y : ℝ) : ℝ := cuspBump (scaleHeight r y)

def oneForm (r : ℝ) : OneForm := fun _ y => (amplitude r y, 0)

theorem amplitude_smooth (r : ℝ) : ContDiff ℝ ∞ (amplitude r) :=
  cuspBump_smooth.comp ((contDiff_const.mul contDiff_id).add contDiff_const)

theorem amplitude_zero (r y : ℝ) (hr : 1 ≤ r) (hy : y ≤ 2 ∨ 5 ≤ y) : amplitude r y = 0 := by
  apply cuspBump_zero_of_height_outside
  rcases hy with hy | hy
  · left
    unfold scaleHeight shift
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ r by linarith)
      (show y - 2 ≤ 0 by linarith)]
  · right
    unfold scaleHeight shift
    nlinarith [mul_nonneg (show 0 ≤ r - 1 by linarith) (show 0 ≤ y - 2 by linarith)]

theorem amplitude_deriv (r y : ℝ) :
    deriv (amplitude r) y = deriv cuspBump (scaleHeight r y) * r := by
  have hb : Differentiable ℝ cuspBump :=
    (contDiff_infty.mp cuspBump_smooth 1).differentiable (by decide)
  have hMul : HasDerivAt (fun t : ℝ => r * t) r y := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id y).const_mul r
  have ht : HasDerivAt (scaleHeight r) r y := by
    change HasDerivAt (fun t : ℝ => r * t + shift r) r y
    exact hMul.add_const (shift r)
  change deriv (fun t => cuspBump (scaleHeight r t)) y = _
  exact (((hb (scaleHeight r y)).hasDerivAt).comp y ht).deriv

theorem oneForm_coclosed (r x y : ℝ) : codifferential (oneForm r) x y = 0 := by
  rw [codifferential_eq_coordinateDivergence]
  simp [oneForm]

theorem oneForm_same_on_high_orbit (r : ℝ) {z w : ℍ}
    (hz : 1 < z.im) (hw : 1 < w.im) (h : orbitPoint w = orbitPoint z) :
    oneForm r w.re w.im = oneForm r z.re z.im := by
  obtain ⟨m, hm⟩ := (HighInfinityCusp.high_orbitPoint_eq_iff_even_translate le_rfl hz hw).mp h
  have him : w.im = z.im := by
    simpa [Complex.add_im, Complex.mul_im] using congrArg Complex.im hm
  simp only [oneForm, him]

def covariantComponents (r y : ℝ) : ℝ × ℝ :=
  (-(christoffel_xy_x y) * amplitude r y,
    deriv (amplitude r) y - christoffel_xy_x y * amplitude r y)

theorem covariant_norm_density (r y : ℝ) (hy : 0 < y) :
    y ^ 2 * ((covariantComponents r y).1 ^ 2 + (covariantComponents r y).2 ^ 2) =
      amplitude r y ^ 2 + (y * deriv (amplitude r) y + amplitude r y) ^ 2 := by
  rw [covariantComponents, christoffel_xy_x_eq hy]
  dsimp
  field_simp [hy.ne'] <;> ring

end
end ManuscriptAudit.CoulombScaledCuspForms

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CoulombScaledCuspForms.amplitude_smooth,
      ``ManuscriptAudit.CoulombScaledCuspForms.amplitude_zero,
      ``ManuscriptAudit.CoulombScaledCuspForms.amplitude_deriv,
      ``ManuscriptAudit.CoulombScaledCuspForms.oneForm_coclosed,
      ``ManuscriptAudit.CoulombScaledCuspForms.oneForm_same_on_high_orbit,
      ``ManuscriptAudit.CoulombScaledCuspForms.covariant_norm_density] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
