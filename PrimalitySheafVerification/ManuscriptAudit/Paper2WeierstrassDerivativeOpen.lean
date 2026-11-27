import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Spectrum.Prime.Topology
import PrimalitySheafVerification.ManuscriptAudit.Paper2WeierstrassReverseProjection

/-! The literal nonsingular affine locus is covered by the two derivative opens at rational points. -/

namespace ManuscriptAudit.Paper2WeierstrassDerivativeOpen

open Polynomial WeierstrassCurve

noncomputable section

variable {R : Type*} [CommRing R]

/-- The first partial derivative as an element of the original affine coordinate ring. -/
def xDerivative (W : WeierstrassCurve R) : W.toAffine.CoordinateRing :=
  AdjoinRoot.mk W.toAffine.polynomial W.toAffine.polynomialX

/-- The second partial derivative in the original coordinate ring. -/
def yDerivative (W : WeierstrassCurve R) : W.toAffine.CoordinateRing :=
  AdjoinRoot.mk W.toAffine.polynomial W.toAffine.polynomialY

theorem original_yDerivative (W : WeierstrassCurve R) :
    Paper2WeierstrassEtaleProjection.yDerivative W = yDerivative W := by
  unfold Paper2WeierstrassEtaleProjection.yDerivative yDerivative
  congr 1
  unfold Affine.polynomial Affine.polynomialY
  simp only [derivative_sub, derivative_add, derivative_X_pow, derivative_C_mul,
    derivative_X, derivative_C, add_zero, sub_zero, mul_one, pow_one, map_natCast, map_ofNat]
  ring

theorem reversed_xDerivative (W : WeierstrassCurve R) :
    Paper2WeierstrassReverseProjection.swapPresentation W (xDerivative W) =
      -AdjoinRoot.mk (Paper2WeierstrassReverseProjection.polynomialInX W)
        (Paper2WeierstrassReverseProjection.polynomialInX W).derivative := by
  let f := Paper2WeierstrassReverseProjection.polynomialInX W
  change AdjoinRoot.mk f (Bivariate.swap W.toAffine.polynomialX) = -AdjoinRoot.mk f f.derivative
  rw [← map_neg]
  congr 1
  unfold f Paper2WeierstrassReverseProjection.polynomialInX Cubic.toPoly Affine.polynomialX
  simp only [map_add, map_sub, map_mul, map_pow, Bivariate.swap_C, Bivariate.swap_Y,
    Polynomial.map_add, Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
    Cubic.a, Cubic.b, Cubic.c, Cubic.d, map_one, one_mul, C_sub, derivative_add, derivative_C,
    derivative_C_mul, derivative_X_pow, derivative_X, derivative_sub, derivative_neg, derivative_mul,
    derivative_pow, mul_one, one_mul, zero_mul, mul_zero, add_zero, zero_add, sub_zero,
    map_natCast, map_ofNat]
  ring

variable {K : Type*} [Field K]

/-- The kernel of genuine quotient-ring evaluation at an affine rational point. -/
def rationalPoint (W : WeierstrassCurve K) (x y : K) (h : W.toAffine.Equation x y) :
    PrimeSpectrum W.toAffine.CoordinateRing where
  asIdeal := RingHom.ker (AdjoinRoot.evalEval h)
  isPrime := RingHom.ker_isPrime _

theorem mem_x_open (W : WeierstrassCurve K) (x y : K) (h : W.toAffine.Equation x y) :
    rationalPoint W x y h ∈ PrimeSpectrum.basicOpen (xDerivative W) ↔
      W.toAffine.polynomialX.evalEval x y ≠ 0 := by
  rw [PrimeSpectrum.mem_basicOpen]
  have h₀ : W.toAffine.polynomial.evalEval x y = 0 := h
  change AdjoinRoot.evalEval h₀ (AdjoinRoot.mk W.toAffine.polynomial W.toAffine.polynomialX) ≠ 0 ↔ _
  rw [AdjoinRoot.evalEval_mk h₀ W.toAffine.polynomialX]

theorem mem_y_open (W : WeierstrassCurve K) (x y : K) (h : W.toAffine.Equation x y) :
    rationalPoint W x y h ∈ PrimeSpectrum.basicOpen (yDerivative W) ↔
      W.toAffine.polynomialY.evalEval x y ≠ 0 := by
  rw [PrimeSpectrum.mem_basicOpen]
  have h₀ : W.toAffine.polynomial.evalEval x y = 0 := h
  change AdjoinRoot.evalEval h₀ (AdjoinRoot.mk W.toAffine.polynomial W.toAffine.polynomialY) ≠ 0 ↔ _
  rw [AdjoinRoot.evalEval_mk h₀ W.toAffine.polynomialY]

theorem nonsingular_iff_mem_derivative_opens (W : WeierstrassCurve K) (x y : K)
    (h : W.toAffine.Equation x y) :
    W.toAffine.Nonsingular x y ↔
      rationalPoint W x y h ∈ PrimeSpectrum.basicOpen (xDerivative W) ∨
        rationalPoint W x y h ∈ PrimeSpectrum.basicOpen (yDerivative W) := by
  rw [mem_x_open, mem_y_open, Affine.Nonsingular, and_iff_right h]

end
end ManuscriptAudit.Paper2WeierstrassDerivativeOpen

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper2WeierstrassDerivativeOpen.original_yDerivative,
      ``ManuscriptAudit.Paper2WeierstrassDerivativeOpen.reversed_xDerivative,
      ``ManuscriptAudit.Paper2WeierstrassDerivativeOpen.mem_x_open,
      ``ManuscriptAudit.Paper2WeierstrassDerivativeOpen.mem_y_open,
      ``ManuscriptAudit.Paper2WeierstrassDerivativeOpen.nonsingular_iff_mem_derivative_opens] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
