import Lean.Util.CollectAxioms
import Mathlib.Algebra.Lie.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Linarith

/-! Positivity of the gauge metric restricts the complex Lie algebra. -/

namespace ManuscriptAudit.Paper10ComplexGaugeMetric

section Bilinear

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- A complex-bilinear form with positive real diagonal is possible only on the zero space. -/
theorem complex_bilinear_positive_forces_zero (B : E →ₗ[ℂ] E →ₗ[ℂ] ℂ)
    (hPos : ∀ x ≠ 0, 0 < (B x x).re) (x : E) : x = 0 := by
  by_contra hx
  have hi : Complex.I • x ≠ 0 := smul_ne_zero Complex.I_ne_zero hx
  have hRotate : B (Complex.I • x) (Complex.I • x) = -B x x := by
    rw [map_smul, LinearMap.smul_apply, map_smul]
    change Complex.I * (Complex.I * B x x) = -B x x
    rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
  have h := hPos (Complex.I • x) hi
  rw [hRotate, Complex.neg_re] at h
  linarith only [h, hPos x hx]

end Bilinear

section Adjoint

variable {L : Type*} [LieRing L] [Module ℂ L] [LieAlgebra ℂ L]

/-- Even a real-valued positive pairing on the underlying additive group forces
the full complex Lie bracket to vanish if all adjoint directions are skew. -/
theorem positive_adInvariant_forces_abelian (B : L →+ L →+ ℝ)
    (hPos : ∀ x ≠ 0, 0 < B x x)
    (hInv : ∀ x y z, B ⁅x, y⁆ z = -B y ⁅x, z⁆) (x y : L) : ⁅x, y⁆ = 0 := by
  by_contra hxy
  have hIy : ⁅Complex.I • x, y⁆ ≠ 0 := by
    rw [smul_lie]
    exact smul_ne_zero Complex.I_ne_zero hxy
  have hSquare : ⁅Complex.I • x, ⁅Complex.I • x, y⁆⁆ = -⁅x, ⁅x, y⁆⁆ := by
    calc
      _ = Complex.I • ⁅x, Complex.I • ⁅x, y⁆⁆ := by rw [smul_lie, smul_lie]
      _ = _ := by rw [lie_smul, smul_smul, Complex.I_mul_I, neg_one_smul]
  have hx := hInv x y ⁅x, y⁆
  have hi := hInv (Complex.I • x) y ⁅Complex.I • x, y⁆
  rw [hSquare, map_neg, neg_neg] at hi
  linarith only [hx, hi, hPos ⁅x, y⁆ hxy, hPos ⁅Complex.I • x, y⁆ hIy]

end Adjoint
section AdjointCurves

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Invariance along differentiable real curves gives skewness at the identity. -/
theorem skew_from_invariant_curves (B : E →L[ℝ] E →L[ℝ] ℝ) (a b : ℝ → E)
    (u v : E) (ha : HasDerivAt a u 0) (hb : HasDerivAt b v 0)
    (hInv : ∀ t, B (a t) (b t) = B (a 0) (b 0)) :
    B u (b 0) = -B (a 0) v := by
  have hBa : HasDerivAt (fun t => B (a t)) (B u) 0 :=
    B.hasFDerivAt.comp_hasDerivAt 0 ha
  have hPair := hBa.clm_apply hb
  have hFunction : (fun t => B (a t) (b t)) = fun _ => B (a 0) (b 0) :=
    funext hInv
  have hSum : B u (b 0) + B (a 0) v = 0 := by
    calc
      _ = deriv (fun t => B (a t) (b t)) 0 := hPair.deriv.symm
      _ = _ := by rw [hFunction, deriv_const]
  linarith only [hSum]

end AdjointCurves

end ManuscriptAudit.Paper10ComplexGaugeMetric

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper10ComplexGaugeMetric.complex_bilinear_positive_forces_zero,
      ``ManuscriptAudit.Paper10ComplexGaugeMetric.positive_adInvariant_forces_abelian,
      ``ManuscriptAudit.Paper10ComplexGaugeMetric.skew_from_invariant_curves] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
