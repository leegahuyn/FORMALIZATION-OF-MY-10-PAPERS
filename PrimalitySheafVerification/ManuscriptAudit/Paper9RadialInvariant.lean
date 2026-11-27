import Lean.Util.CollectAxioms
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import PrimalitySheafVerification.ManuscriptAudit.LiteralCuspTruncation

/-!
# The literal Γ(2)-invariant radial sector is constant

Physical pp. 440–441 restrict the calculation to Γ(2)-invariant
functions depending on t=2πy. For the actual Möbius action, this
hypothesis forces every such scalar function to be constant. No
continuity or differentiability is needed.
-/

namespace ManuscriptAudit.Paper9RadialInvariant

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups UpperHalfPlane
open LiteralCuspTruncation (GammaTwo OrbitQuotient orbitPoint)

noncomputable section

private def shearMatrix : SL(2, ℤ) := ⟨!![1, 0; 2, 1], by simp [Matrix.det_fin_two_of]⟩

private theorem shearMatrix_mem : shearMatrix ∈ GammaTwo := by
  rw [CongruenceSubgroup.Gamma_mem]
  change (1 : ZMod 2) = 1 ∧ (0 : ZMod 2) = 0 ∧ (2 : ZMod 2) = 0 ∧ (1 : ZMod 2) = 1
  decide

private def shear : GammaTwo := ⟨shearMatrix, shearMatrix_mem⟩

private def point (x y : ℝ) (hy : 0 < y) : ℍ := ⟨⟨x, y⟩, hy⟩

private theorem shear_denom (z : ℍ) :
    UpperHalfPlane.denom (SpecialLinearGroup.toGL
      ((SpecialLinearGroup.map (Int.castRingHom ℝ)) shearMatrix)) (z : ℂ) = 2 * (z : ℂ) + 1 := by
  rw [ModularGroup.denom_apply]
  norm_num [shearMatrix]

private theorem shear_height (x y : ℝ) (hy : 0 < y) :
    (shear • point x y hy).im = y / ((2 * x + 1) ^ 2 + (2 * y) ^ 2) := by
  change (shearMatrix • point x y hy).im = _
  rw [ModularGroup.im_smul_eq_div_normSq, shear_denom, Complex.normSq_apply]
  norm_num [point, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, pow_two]

private theorem shear_matching_height (y v : ℝ) (hy : 0 < y) (hv : 0 < v) :
    (shear • point (Real.sqrt (y * v) - 1 / 2) y hy).im = 1 / (4 * (y + v)) := by
  rw [shear_height]
  have hx : 2 * (Real.sqrt (y * v) - 1 / 2) + 1 = 2 * Real.sqrt (y * v) := by ring
  rw [hx, mul_pow, Real.sq_sqrt (mul_nonneg hy.le hv.le)]
  have hD : (2 : ℝ) ^ 2 * (y * v) + (2 * y) ^ 2 = 4 * (y + v) * y := by ring
  rw [hD]
  field_simp [hy.ne', (add_pos hy hv).ne'] <;> ring

theorem invariant_height_function_constant {E : Type*} (f : ℝ → E)
    (h : ∀ (g : GammaTwo) (z : ℍ), f (g • z).im = f z.im) :
    ∀ {y v : ℝ}, 0 < y → 0 < v → f y = f v := by
  intro y v hy hv
  have hY := h shear (point (Real.sqrt (y * v) - 1 / 2) y hy)
  have hV := h shear (point (Real.sqrt (v * y) - 1 / 2) v hv)
  rw [shear_matching_height y v hy hv] at hY
  rw [shear_matching_height v y hv hy, add_comm v y] at hV
  exact hY.symm.trans hV

theorem quotient_function_constant_of_radial {E : Type*} (F : OrbitQuotient → E)
    (f : ℝ → E) (h : ∀ z : ℍ, F (orbitPoint z) = f z.im) :
    ∀ a b : OrbitQuotient, F a = F b := by
  have hInv (g : GammaTwo) (z : ℍ) : f (g • z).im = f z.im := by
    have hQ : orbitPoint (g • z) = orbitPoint z := Quotient.sound ⟨g, rfl⟩
    rw [← h (g • z), ← h z, hQ]
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro z w
  change F (orbitPoint z) = F (orbitPoint w)
  rw [h z, h w]
  exact invariant_height_function_constant f hInv z.im_pos w.im_pos

theorem quotient_function_constant_of_modular_time {E : Type*} (F : OrbitQuotient → E)
    (u : ℝ → E) (h : ∀ z : ℍ, F (orbitPoint z) = u (2 * Real.pi * z.im)) :
    ∀ a b : OrbitQuotient, F a = F b :=
  quotient_function_constant_of_radial F (fun y => u (2 * Real.pi * y)) h

end
end ManuscriptAudit.Paper9RadialInvariant

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper9RadialInvariant.invariant_height_function_constant,
      ``ManuscriptAudit.Paper9RadialInvariant.quotient_function_constant_of_radial,
      ``ManuscriptAudit.Paper9RadialInvariant.quotient_function_constant_of_modular_time] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
