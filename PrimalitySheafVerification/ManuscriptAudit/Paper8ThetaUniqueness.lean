import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.MaassLaplacian
import PrimalitySheafVerification.ManuscriptAudit.Paper8XiShadow
import PrimalitySheafVerification.ManuscriptAudit.ThetaCuspPolarData
import PrimalitySheafVerification.ManuscriptAudit.ThetaHolomorphicMultiplier

/-!
The all-cusp uniqueness step on physical p. 327 needs more than the
negative coefficients extracted on p. 326 and the shadow. The actual
weight-one-half theta provides a holomorphic ambiguity on Γ(2).
-/

namespace ManuscriptAudit.Paper8ThetaUniqueness

open Set
open MaassLaplacian Paper8XiShadow ThetaCuspPolarData ThetaHolomorphicMultiplier
open LiteralCuspTruncation (GammaTwo)
open scoped MatrixGroups UpperHalfPlane

noncomputable section

def thetaField : Paper8XiShadow.Field := fun x y => jacobiTheta (complexPoint x y)

theorem theta_has_zero_shadow (x y : ℝ) (hy : 0 < y) :
    xiHalf thetaField x y = 0 := by
  have hθ := (differentiableAt_jacobiTheta
    (show 0 < (complexPoint x y).im by simpa only [complexPoint_im] using hy)).hasDerivAt
  have hx : partialX thetaField x y = deriv jacobiTheta (complexPoint x y) :=
    (horizontal_derivative hθ).deriv
  have hy' : partialY thetaField x y = Complex.I * deriv jacobiTheta (complexPoint x y) :=
    (vertical_derivative hθ).deriv
  have hBar : dBar thetaField x y = 0 := by
    rw [dBar, hx, hy', ← mul_assoc, Complex.I_mul_I, neg_one_mul, add_neg_cancel, zero_div]
  rw [xiHalf, hBar, map_zero, mul_zero]

theorem zero_has_zero_shadow (x y : ℝ) :
    xiHalf (fun _ _ => 0) x y = 0 := by
  simp [xiHalf, dBar, partialX, partialY]

theorem thetaField_ne_zero : thetaField ≠ (fun _ _ => 0) := by
  intro h
  have hT : thetaField 0 1 = 0 := congrFun (congrFun h 0) 1
  have hPoint : complexPoint 0 1 = Complex.I := by simp [complexPoint]
  rw [thetaField, hPoint] at hT
  exact ThetaGlobalSection.jacobiTheta_ne_zero_upperHalfPlane UpperHalfPlane.I hT

theorem theta_and_zero_same_polar_data_and_shadow :
    (∀ i : Fin 3, ∀ R ∈ Ioo (0 : ℝ) 1, ∀ n,
      negativeCoefficient (profileQ i) R n =
        negativeCoefficient (fun _ => 0) R n) ∧
    (∀ x y : ℝ, 0 < y → xiHalf thetaField x y = xiHalf (fun _ _ => 0) x y) ∧
    thetaField ≠ (fun _ _ => 0) :=
  ⟨nonzero_profiles_with_zero_polar_data.1, fun x y hy =>
    (theta_has_zero_shadow x y hy).trans (zero_has_zero_shadow x y).symm,
    thetaField_ne_zero⟩

theorem theta_and_zero_admit_same_multiplier :
    ∃ v : GammaTwo → ℂ, (∀ γ, ‖v γ‖ = 1) ∧
      ∀ f ∈ ({jacobiTheta, fun _ : ℂ => 0} : Set (ℂ → ℂ)),
        ∀ (γ : GammaTwo) (z : ℍ),
          f ((γ • z : ℍ) : ℂ) = v γ * halfFactor (γ : SL(2, ℤ)) z * f (z : ℂ) := by
  refine ⟨phase, phase_norm, ?_⟩
  intro f hf γ z
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
  rcases hf with rfl | rfl
  · exact theta_transformation γ z
  · simp

end
end ManuscriptAudit.Paper8ThetaUniqueness

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ThetaUniqueness.theta_has_zero_shadow,
      ``ManuscriptAudit.Paper8ThetaUniqueness.zero_has_zero_shadow,
      ``ManuscriptAudit.Paper8ThetaUniqueness.thetaField_ne_zero,
      ``ManuscriptAudit.Paper8ThetaUniqueness.theta_and_zero_same_polar_data_and_shadow,
      ``ManuscriptAudit.Paper8ThetaUniqueness.theta_and_zero_admit_same_multiplier] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
