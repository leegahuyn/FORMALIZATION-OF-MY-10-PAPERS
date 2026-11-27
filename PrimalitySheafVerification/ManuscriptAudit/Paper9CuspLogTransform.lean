import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper9EisensteinHeightEquation

/-!
# Exact logarithmic form of the zero horizontal mode

The profile y^(1/2) g(log y) converts the printed high-cusp L to
the constant-coefficient expression g'' − g/4.
-/

namespace ManuscriptAudit.Paper9CuspLogTransform

open Set Filter Paper9EisensteinHeightEquation
open Paper9HighCuspSection Paper9HighCuspCoordinates Paper9PrintedLaplacianSign
open scoped UpperHalfPlane Topology

noncomputable section

def weightedLogProfile (g : ℝ → ℂ) (y : ℝ) : ℂ :=
  heightPower (1 / 2) y * g (Real.log y)

private theorem logComp_hasDerivAt (g : ℝ → ℂ) (hg : Differentiable ℝ g) {y : ℝ}
    (hy : y ≠ 0) :
    HasDerivAt (fun t => g (Real.log t)) ((y : ℂ)⁻¹ * deriv g (Real.log y)) y := by
  have h := (hg (Real.log y)).hasDerivAt.scomp y (Real.hasDerivAt_log hy)
  simpa only [Function.comp_def, Algebra.smul_def, Complex.ofReal_inv] using h

theorem weightedLogProfile_hasDerivAt (g : ℝ → ℂ) (hg : Differentiable ℝ g)
    {y : ℝ} (hy : 0 < y) :
    HasDerivAt (weightedLogProfile g)
      (weightedLogProfile (fun t => (1 / 2 : ℂ) * g t + deriv g t) y / (y : ℂ)) y := by
  have hC : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have h := (heightPower_hasDerivAt (1 / 2 : ℂ) hy.ne').mul (logComp_hasDerivAt g hg hy.ne')
  convert h using 1 <;> simp only [weightedLogProfile] <;> field_simp [hC] <;> ring

theorem weightedLogProfile_second (g : ℝ → ℂ)
    (hg : Differentiable ℝ g) (hg' : Differentiable ℝ (deriv g)) {y : ℝ} (hy : 0 < y) :
    deriv (deriv (weightedLogProfile g)) y =
      weightedLogProfile (fun t => deriv (deriv g) t - (1 / 4 : ℂ) * g t) y / (y : ℂ) ^ 2 := by
  let b : ℝ → ℂ := fun t => (1 / 2 : ℂ) * g t + deriv g t
  have hb : Differentiable ℝ b := (hg.const_mul _).add hg'
  have hLocal : deriv (weightedLogProfile g) =ᶠ[𝓝 y]
      (fun t : ℝ => weightedLogProfile b t / (t : ℂ)) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact (weightedLogProfile_hasDerivAt g hg ht).deriv
  have hC : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hB := weightedLogProfile_hasDerivAt b hb hy
  have h := hB.div ((hasDerivAt_id y).ofReal_comp) hC
  have hb' (t : ℝ) : deriv b t = (1 / 2 : ℂ) * deriv g t + deriv (deriv g) t :=
    (((hg t).hasDerivAt.const_mul (1 / 2 : ℂ)).add (hg' t).hasDerivAt).deriv
  rw [hLocal.deriv_eq, h.deriv]
  simp only [id_eq, Complex.ofReal_one, weightedLogProfile]
  rw [hb']
  dsimp [b]
  field_simp [hC] <;> ring

theorem printedL_weightedLogProfile (g : ℝ → ℂ)
    (hg : Differentiable ℝ g) (hg' : Differentiable ℝ (deriv g)) (z : ℍ) (hz : 1 < z.im) :
    printedL (coordinates (weightedLogProfile g)) z =
      weightedLogProfile (fun t => deriv (deriv g) t - (1 / 4 : ℂ) * g t) z.im := by
  have hC : (z.im : ℂ) ≠ 0 := by exact_mod_cast z.im_ne_zero
  rw [printedL_high _ z hz, weightedLogProfile_second g hg hg' z.im_pos]
  field_simp [hC]

end
end ManuscriptAudit.Paper9CuspLogTransform

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper9CuspLogTransform.weightedLogProfile_hasDerivAt,
      ``ManuscriptAudit.Paper9CuspLogTransform.weightedLogProfile_second,
      ``ManuscriptAudit.Paper9CuspLogTransform.printedL_weightedLogProfile] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
