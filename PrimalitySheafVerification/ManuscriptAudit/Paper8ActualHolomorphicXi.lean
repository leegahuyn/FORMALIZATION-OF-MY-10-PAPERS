import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8HolomorphicPartPhase
import PrimalitySheafVerification.ManuscriptAudit.Paper8XiShadow

/-!
# The actual holomorphic part has zero ξ-image

The coordinate calculation uses the same real derivatives and conjugated
operator as physical pp. 332 and 338. The correction contributes its own
ξ-image under the pointwise differentiability required by that operator.
-/

namespace ManuscriptAudit.Paper8ActualHolomorphicXi

open MaassLaplacian (complexPoint complexPoint_im partialX partialY horizontal_derivative vertical_derivative)
open Paper8XiShadow (Field dBar xiHalf)
open Paper8HolomorphicPartPhase (normalizedPart normalizedPart_differentiableOn)

noncomputable section

theorem dBar_holomorphic_zero {f : ℂ → ℂ} {x y : ℝ}
    (h : DifferentiableAt ℂ f (complexPoint x y)) :
    dBar (fun u v => f (complexPoint u v)) x y = 0 := by
  rw [dBar, partialX, partialY, (horizontal_derivative h.hasDerivAt).deriv,
    (vertical_derivative h.hasDerivAt).deriv, ← mul_assoc, Complex.I_mul_I]
  simp

theorem xiHalf_holomorphic_zero {f : ℂ → ℂ} {x y : ℝ}
    (h : DifferentiableAt ℂ f (complexPoint x y)) :
    xiHalf (fun u v => f (complexPoint u v)) x y = 0 := by
  simp only [xiHalf, dBar_holomorphic_zero h, map_zero, mul_zero]

private theorem normalizedPart_differentiable_at {x y : ℝ} (hy : 0 < y) :
    DifferentiableAt ℂ normalizedPart (complexPoint x y) := by
  have hOpen : IsOpen {τ : ℂ | 0 < τ.im} := isOpen_lt continuous_const Complex.continuous_im
  have hPoint : complexPoint x y ∈ {τ : ℂ | 0 < τ.im} := by
    change 0 < (complexPoint x y).im
    simpa only [complexPoint_im] using hy
  exact normalizedPart_differentiableOn.differentiableAt (hOpen.mem_nhds hPoint)

theorem xiHalf_normalizedPart_zero {x y : ℝ} (hy : 0 < y) :
    xiHalf (fun u v => normalizedPart (complexPoint u v)) x y = 0 :=
  xiHalf_holomorphic_zero (normalizedPart_differentiable_at hy)

theorem xiHalf_normalizedPart_add_correction {R : Field} {x y : ℝ} (hy : 0 < y)
    (hRX : DifferentiableAt ℝ (fun t => R t y) x)
    (hRY : DifferentiableAt ℝ (fun t => R x t) y) :
    xiHalf (fun u v => normalizedPart (complexPoint u v) + R u v) x y = xiHalf R x y := by
  have h := (normalizedPart_differentiable_at (x := x) hy).hasDerivAt
  have hX := ((horizontal_derivative h).add hRX.hasDerivAt).deriv
  have hY := ((vertical_derivative h).add hRY.hasDerivAt).deriv
  have hCR (w : ℂ) : w + Complex.I * (Complex.I * w) = 0 := by
    rw [← mul_assoc, Complex.I_mul_I]
    simp
  have hBar : dBar (fun u v => normalizedPart (complexPoint u v) + R u v) x y = dBar R x y := by
    rw [dBar, dBar, partialX, partialX, partialY, partialY, hX, hY]
    congr 1
    calc
      _ = (deriv normalizedPart (complexPoint x y) +
          Complex.I * (Complex.I * deriv normalizedPart (complexPoint x y))) +
          (deriv (fun t => R t y) x + Complex.I * deriv (fun t => R x t) y) := by ring
      _ = _ := by rw [hCR, zero_add]
  rw [xiHalf, xiHalf, hBar]

end
end ManuscriptAudit.Paper8ActualHolomorphicXi

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ActualHolomorphicXi.dBar_holomorphic_zero,
      ``ManuscriptAudit.Paper8ActualHolomorphicXi.xiHalf_holomorphic_zero,
      ``ManuscriptAudit.Paper8ActualHolomorphicXi.xiHalf_normalizedPart_zero,
      ``ManuscriptAudit.Paper8ActualHolomorphicXi.xiHalf_normalizedPart_add_correction] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
