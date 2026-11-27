import Lean.Util.CollectAxioms
import Mathlib.Tactic.LinearCombination
import PrimalitySheafVerification.ManuscriptAudit.MaassLaplacian

/-! The derivative factorization at weight −1/2 and spectral level 3/16. -/

namespace ManuscriptAudit.Paper8NegativeHalfMaassFactorization

open MaassLaplacian

noncomputable section

abbrev Profile := ℝ → ℝ → ℂ

def raising (F : Profile) (x y : ℝ) : ℂ :=
  Complex.I*(y : ℂ)*partialX F x y + (y : ℂ)*partialY F x y - (1/4 : ℂ)*F x y

def adjointExpression (F : Profile) (x y : ℝ) : ℂ :=
  Complex.I*(y : ℂ)*partialX F x y - (y : ℂ)*partialY F x y + (3/4 : ℂ)*F x y

private theorem raising_x (F : Profile) (x y : ℝ)
    (hx : DifferentiableAt ℝ (fun t => F t y) x)
    (hxx : DifferentiableAt ℝ (fun t => partialX F t y) x)
    (hyx : DifferentiableAt ℝ (fun t => partialY F t y) x) :
    partialX (raising F) x y = Complex.I*(y : ℂ)*partialX (partialX F) x y +
      (y : ℂ)*partialX (partialY F) x y - (1/4 : ℂ)*partialX F x y := by
  have h₁ := hxx.hasDerivAt.const_mul (Complex.I*(y : ℂ))
  have h₂ := hyx.hasDerivAt.const_mul (y : ℂ)
  have h₃ := hx.hasDerivAt.const_mul (1/4 : ℂ)
  exact ((h₁.add h₂).sub h₃).deriv

private theorem raising_y (F : Profile) (x y : ℝ)
    (hy : DifferentiableAt ℝ (F x) y)
    (hxy : DifferentiableAt ℝ (partialX F x) y)
    (hyy : DifferentiableAt ℝ (partialY F x) y) :
    partialY (raising F) x y =
      Complex.I*partialX F x y + Complex.I*(y : ℂ)*partialY (partialX F) x y +
      partialY F x y + (y : ℂ)*partialY (partialY F) x y -
      (1/4 : ℂ)*partialY F x y := by
  have hY : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 y := by
    simpa only [id_eq, Complex.ofReal_one] using (hasDerivAt_id y).ofReal_comp
  have h₁ := (hY.const_mul Complex.I).mul hxy.hasDerivAt
  have h₂ := hY.mul hyy.hasDerivAt
  have h₃ := hy.hasDerivAt.const_mul (1/4 : ℂ)
  have h := ((h₁.add h₂).sub h₃).deriv
  change partialY (raising F) x y = _ at h
  rw [h]
  change Complex.I*1*partialX F x y + Complex.I*(y : ℂ)*deriv (partialX F x) y +
      (1*deriv (F x) y + (y : ℂ)*deriv (partialY F x) y) -
        (1/4 : ℂ)*deriv (F x) y =
    Complex.I*partialX F x y + Complex.I*(y : ℂ)*deriv (partialX F x) y +
      deriv (F x) y + (y : ℂ)*deriv (partialY F x) y -
        (1/4 : ℂ)*deriv (F x) y
  ring

theorem factorization (F : Profile) (x y : ℝ)
    (hx : DifferentiableAt ℝ (fun t => F t y) x)
    (hy : DifferentiableAt ℝ (F x) y)
    (hxx : DifferentiableAt ℝ (fun t => partialX F t y) x)
    (hxy : DifferentiableAt ℝ (partialX F x) y)
    (hyx : DifferentiableAt ℝ (fun t => partialY F t y) x)
    (hyy : DifferentiableAt ℝ (partialY F x) y)
    (hMixed : partialX (partialY F) x y = partialY (partialX F) x y) :
    maassDelta (-1/2) F x y = adjointExpression (raising F) x y + (3/16 : ℂ)*F x y := by
  unfold maassDelta adjointExpression
  rw [raising_x F x y hx hxx hyx, raising_y F x y hy hxy hyy, hMixed]
  unfold raising
  norm_num [Complex.ofReal_div]
  linear_combination (-(y : ℂ)^2*partialX (partialX F) x y) * Complex.I_sq

end
end ManuscriptAudit.Paper8NegativeHalfMaassFactorization

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8NegativeHalfMaassFactorization.factorization
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
