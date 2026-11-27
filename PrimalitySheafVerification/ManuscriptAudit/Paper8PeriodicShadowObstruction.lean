import Lean.Util.CollectAxioms
import Mathlib.Analysis.Calculus.Deriv.Shift
import PrimalitySheafVerification.ManuscriptAudit.Paper8XiShadow
import PrimalitySheafVerification.ManuscriptAudit.Paper8KroneckerShadowPhase
import PrimalitySheafVerification.ManuscriptAudit.Paper8KroneckerShadowNonzero

/-!
# The exact unit-period and nonzero shadow assertions cannot both hold

Physical p. 337 discusses period one, while p. 338 prescribes a nonzero
multiple of the Kronecker unary theta. The actual ξ operator preserves unit
periodicity, and the specified theta has nontrivial translation phase.
-/

namespace ManuscriptAudit.Paper8PeriodicShadowObstruction

open Filter
open MaassLaplacian (complexPoint partialX partialY)
open Paper8XiShadow (Field dBar xiHalf)
open Paper8HolomorphicPartPhase (normalizationPhase_ne_one)
open Paper8KroneckerShadow (unaryShadow)
open Paper8KroneckerShadowPhase
open Paper8KroneckerShadowNonzero

open scoped Topology

theorem xiHalf_add_one_of_periodic {F : Field}
    (hPeriod : ∀ x y : ℝ, 0 < y → F (x + 1) y = F x y)
    {x y : ℝ} (hy : 0 < y) : xiHalf F (x + 1) y = xiHalf F x y := by
  have hX : (fun t : ℝ => F (t + 1) y) = (fun t : ℝ => F t y) :=
    funext fun t => hPeriod t y hy
  have hDX : partialX F (x + 1) y = partialX F x y := by
    unfold partialX
    calc
      _ = deriv (fun t : ℝ => F (t + 1) y) x :=
        (deriv_comp_add_const (fun t : ℝ => F t y) 1 x).symm
      _ = _ := congrArg (fun f : ℝ → ℂ => deriv f x) hX
  have hY : (fun t : ℝ => F (x + 1) t) =ᶠ[𝓝 y] (fun t : ℝ => F x t) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht using hPeriod x t ht
  have hDY : partialY F (x + 1) y = partialY F x y := hY.deriv_eq
  rw [xiHalf, xiHalf, dBar, dBar, hDX, hDY]

theorem shadowPhase_ne_one : shadowPhase ≠ 1 := by
  rw [shadowPhase_eq_inverse_normalization]
  intro h
  exact normalizationPhase_ne_one (by simpa only [inv_inv, inv_one] using congrArg Inv.inv h)

private theorem complexPoint_add_one (x y : ℝ) :
    complexPoint (x + 1) y = complexPoint x y + 1 := by
  unfold complexPoint
  rw [Complex.ofReal_add, Complex.ofReal_one]
  ring

theorem printed_period_and_shadow_incompatible {F : Field} {κ : ℂ}
    (hκ : κ ≠ 0)
    (hPeriod : ∀ x y : ℝ, 0 < y → F (x + 1) y = F x y)
    (hShadow : ∀ x y : ℝ, 0 < y → xiHalf F x y = κ * unaryShadow (complexPoint x y)) :
    False := by
  obtain ⟨z, hz, hNonzero⟩ := unaryShadow_nonzero_on_upper_half_plane
  have hPoint : complexPoint z.re z.im = z := Complex.re_add_im z
  have hPeriodXi := xiHalf_add_one_of_periodic hPeriod (x := z.re) hz
  rw [hShadow (z.re + 1) z.im hz, hShadow z.re z.im hz,
    complexPoint_add_one, hPoint, unaryShadow_add_one hz] at hPeriodXi
  have hCancel := mul_left_cancel₀ hκ hPeriodXi
  exact shadowPhase_ne_one (mul_right_cancel₀ hNonzero
    (by simpa only [one_mul] using hCancel))

end ManuscriptAudit.Paper8PeriodicShadowObstruction

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8PeriodicShadowObstruction.xiHalf_add_one_of_periodic,
      ``ManuscriptAudit.Paper8PeriodicShadowObstruction.shadowPhase_ne_one,
      ``ManuscriptAudit.Paper8PeriodicShadowObstruction.printed_period_and_shadow_incompatible] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
