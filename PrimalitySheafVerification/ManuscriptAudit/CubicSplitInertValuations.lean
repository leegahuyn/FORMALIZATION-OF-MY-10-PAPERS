import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CyclotomicFiniteGroupValuation
import PrimalitySheafVerification.ManuscriptAudit.CubicRotationQuadratic

/-! Even valuations at every inert coefficient prime for actual split centered cubic counts. -/

namespace ManuscriptAudit.CubicSplitInertValuations

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate
open CubicThreeTorsionCard CubicCubeRotation CubicRotationQuadratic

noncomputable section

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {A z : K}

/-- If the base field contains a primitive cube root of unity, every prime congruent to two
modulo three occurs to an even exponent in the number of rational projective points. -/
theorem projective_count_factorization_even
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0)
    (hz : z ^ 3 = 1) (hz₁ : z ≠ 1)
    (l : ℕ) [Fact l.Prime] (hl : l % 3 = 2) :
    Even ((Nat.card (shortCubic (0 : K) A).toProjective.Point).factorization l) := by
  have hΔ := shortCubic_discriminant_ne_zero h₂ h₃ hA
  let r : (Curve A).Point →+ (Curve A).Point := rotate z hz hΔ
  let R : (Curve A).Point ≃+ (Curve A).Point :=
    { toFun := r
      invFun := fun x => r (r x)
      left_inv := fun x => rotate_cube hz hΔ x
      right_inv := fun x => rotate_cube hz hΔ x
      map_add' := map_add r }
  letI : Finite (Curve A).Point :=
    Finite.of_injective _ (Curve A).nonsingularPointEquiv.injective
  have hf := CyclotomicFiniteGroupValuation.additive_factorization_even l hl R
    (rotate_sum_eq_zero h₂ h₃ hA hz hz₁ hΔ)
  have hc : Nat.card (shortCubic (0 : K) A).toProjective.Point = Nat.card (Curve A).Point :=
    Nat.card_congr
      (Projective.Point.toAffineAddEquiv (W := (shortCubic (0 : K) A).toProjective)).toEquiv
  rw [hc]
  exact hf

end
end ManuscriptAudit.CubicSplitInertValuations

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicSplitInertValuations.projective_count_factorization_even
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
