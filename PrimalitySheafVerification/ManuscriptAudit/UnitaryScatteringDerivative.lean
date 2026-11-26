import Lean.Util.CollectAxioms
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Linarith

/-!
# Real-parameter logarithmic derivatives of unitary matrices

The entrywise derivative of A* A = 1 gives a skew-Hermitian matrix
A* A'. In this parameterization its trace has zero real part.
This checks what unitarity itself implies for the matrix scattering
expression discussed in Paper 9.
-/

namespace ManuscriptAudit.UnitaryScatteringDerivative

open scoped Matrix BigOperators

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem derivative_conj {f : ℝ → ℂ} {a : ℂ} {x : ℝ}
    (h : HasDerivAt f a x) :
    HasDerivAt (fun t => star (f t)) (star a) x := by
  let L : ℂ →L[ℝ] ℂ := Complex.conjCLE.toContinuousLinearMap
  exact L.hasFDerivAt.comp_hasDerivAt x h

/-- The entrywise actual derivative of the unitarity identity. -/
theorem derivative_unitarity_zero (A : ℝ → Matrix n n ℂ) (B : Matrix n n ℂ) (x : ℝ)
    (hA : ∀ i j, HasDerivAt (fun t => A t i j) (B i j) x)
    (hUnit : ∀ t, (A t)ᴴ * A t = 1) :
    Bᴴ * A x + (A x)ᴴ * B = 0 := by
  ext i j : 1
  have hprod (k : n) :
      HasDerivAt (fun t => star (A t k i) * A t k j)
        (star (B k i) * A x k j + star (A x k i) * B k j) x :=
    (derivative_conj (hA k i)).mul (hA k j)
  have hs := HasDerivAt.fun_sum (u := Finset.univ)
    (fun k _ => hprod k)
  have hder : HasDerivAt (fun t => (((A t)ᴴ * A t) i j))
      ((Bᴴ * A x + (A x)ᴴ * B) i j) x := by
    simpa only [Matrix.mul_apply, Matrix.add_apply, Matrix.conjTranspose_apply,
      Finset.sum_add_distrib] using hs
  have hfun : (fun t => (((A t)ᴴ * A t) i j)) = fun _ => (1 : Matrix n n ℂ) i j := by
    funext t
    rw [hUnit]
  rw [hfun] at hder
  exact hder.unique (hasDerivAt_const x ((1 : Matrix n n ℂ) i j))

/-- The logarithmic derivative in the real parameter is skew-Hermitian. -/
theorem logarithmicDerivative_skew (A : ℝ → Matrix n n ℂ) (B : Matrix n n ℂ) (x : ℝ)
    (hA : ∀ i j, HasDerivAt (fun t => A t i j) (B i j) x)
    (hUnit : ∀ t, (A t)ᴴ * A t = 1) :
    (((A x)ᴴ * B)ᴴ) = -((A x)ᴴ * B) := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have h := derivative_unitarity_zero A B x hA hUnit
  calc
    _ = (Bᴴ * A x + (A x)ᴴ * B) - (A x)ᴴ * B := (add_sub_cancel_right _ _).symm
    _ = _ := by rw [h, zero_sub]

theorem trace_logarithmicDerivative_re_zero (A : ℝ → Matrix n n ℂ)
    (B : Matrix n n ℂ) (x : ℝ)
    (hA : ∀ i j, HasDerivAt (fun t => A t i j) (B i j) x)
    (hUnit : ∀ t, (A t)ᴴ * A t = 1) :
    (Matrix.trace ((A x)ᴴ * B)).re = 0 := by
  let D := (A x)ᴴ * B
  have h := logarithmicDerivative_skew A B x hA hUnit
  have hh (i : n) : (D i i).re = 0 := by
    have hi := congrArg (fun P : Matrix n n ℂ => (P i i).re) h
    change (star (D i i)).re = (-D i i).re at hi
    simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at hi
    linarith
  change (Matrix.trace D).re = 0
  simp [Matrix.trace, Complex.re_sum, hh]

end

end ManuscriptAudit.UnitaryScatteringDerivative

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.UnitaryScatteringDerivative.derivative_unitarity_zero,
      ``ManuscriptAudit.UnitaryScatteringDerivative.logarithmicDerivative_skew,
      ``ManuscriptAudit.UnitaryScatteringDerivative.trace_logarithmicDerivative_re_zero] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
