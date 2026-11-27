import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8MaassRectangleEnergy
import PrimalitySheafVerification.ManuscriptAudit.Paper8CuspHolomorphicCoefficient

/-! At the critical spectral value the Green identity forces a holomorphic coefficient. -/

namespace ManuscriptAudit.Paper8CuspCriticalCoefficient

open Set
open MaassLaplacian Paper8NegativeHalfMaassFactorization
open Paper8MaassRectangleAdjoint Paper8MaassRectangleEnergy RectangularIntegral
open Paper8CuspHolomorphicCoefficient

theorem raising_zero_on_interior {a b c d : ℝ} (hc : 0 < c) (F : Profile)
    (hRaise : Continuous (raising F).uncurry)
    (hGreen : box a b c d (density F (adjointExpression (raising F))) =
      box a b c d (density (raising F) (raising F)))
    (hEquation : ∀ z ∈ rectangle a b c d, adjointExpression (raising F) z.1 z.2 = 0)
    {x y : ℝ} (hx : x ∈ Ioo a b) (hy : y ∈ Ioo c d) :
    raising F x y = 0 := by
  have hEq : ∀ z ∈ rectangle a b c d,
      adjointExpression (raising F) z.1 z.2 = ((3/16 - 3/16 : ℝ) : ℂ) * F z.1 z.2 := by
    intro z hz
    simpa only [sub_self, Complex.ofReal_zero, zero_mul] using hEquation z hz
  have hNorm : normSquare a b c d (raising F) = 0 := by
    simpa only [sub_self, zero_mul] using eigenvalue_energy F (3/16) hGreen hEq
  by_contra h
  exact (normSquare_positive hc (raising F) hRaise hx hy h).ne' hNorm

theorem critical_coefficient_holomorphic {a b c d : ℝ} (hc : 0 < c) (F : Profile)
    (hRaise : Continuous (raising F).uncurry)
    (hGreen : box a b c d (density F (adjointExpression (raising F))) =
      box a b c d (density (raising F) (raising F)))
    (hEquation : ∀ z ∈ rectangle a b c d, adjointExpression (raising F) z.1 z.2 = 0)
    {x y : ℝ} (hx : x ∈ Ioo a b) (hy : y ∈ Ioo c d)
    (hF : DifferentiableAt ℝ F.uncurry (x,y)) :
    DifferentiableAt ℂ (coefficient F) (complexPoint x y) :=
  coefficient_complex_differentiable F x y (hc.trans hy.1) hF
    (raising_zero_on_interior hc F hRaise hGreen hEquation hx hy)

end ManuscriptAudit.Paper8CuspCriticalCoefficient

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.Paper8CuspCriticalCoefficient.raising_zero_on_interior,
      ``ManuscriptAudit.Paper8CuspCriticalCoefficient.critical_coefficient_holomorphic] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
