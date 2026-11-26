import Lean.Util.CollectAxioms
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# The scalar bracket and the twisted trace in the printed gauge model

The scalar rule multiplies the reversed matrix product by q.
The automorphism rule applies a unital algebra automorphism to its
right argument. Evaluation on identity endomorphisms distinguishes
these two rules at the printed interior cusp parameter.
-/

namespace ManuscriptAudit.ScalarTwistCompatibility

noncomputable section

variable {A : Type*} [Ring A] [Algebra ℂ A]

def scalarBracket (q : ℂ) (x y : A) : A := x * y - q • (y * x)

def automorphismBracket (σ : A ≃ₐ[ℂ] A) (x y : A) : A := x * y - σ y * x

/-- The two printed matrix commutators cannot agree at a scalar q different from 1. -/
theorem scalar_bracket_ne_automorphism_bracket [Nontrivial A] (q : ℂ) (hq : q ≠ 1)
    (σ : A ≃ₐ[ℂ] A) : scalarBracket (A := A) q ≠ automorphismBracket σ := by
  intro h
  have hOne : (1 : A) - q • (1 : A) = 0 := by
    simpa only [scalarBracket, automorphismBracket, one_mul, map_one, sub_self] using
      congrFun (congrFun h (1 : A)) (1 : A)
  have hAlgebra : algebraMap ℂ A q = 1 := by
    simpa only [Algebra.smul_def, mul_one] using (sub_eq_zero.mp hOne).symm
  exact hq ((algebraMap ℂ A).injective (hAlgebra.trans (map_one (algebraMap ℂ A)).symm))

/-- Scalar-bracket tracelessness for all matrices would force the trace of the identity to vanish. -/
theorem scalar_bracket_trace_one_nonzero (q : ℂ) (hq : q ≠ 1) (trace : A →ₗ[ℂ] ℂ)
    (hTrace : trace 1 ≠ 0) : trace (scalarBracket q (1 : A) 1) ≠ 0 := by
  intro h
  have hOne : trace 1 - q * trace 1 = 0 := by
    simpa only [scalarBracket, one_mul, map_sub, map_smul, smul_eq_mul] using h
  have hProduct : (1 - q) * trace 1 = 0 := by
    rwa [sub_mul, one_mul]
  exact hq ((sub_eq_zero.mp ((mul_eq_zero.mp hProduct).resolve_right hTrace)).symm)

/-- The parameter of Definition 2.1 at the point τ = i. -/
def cuspParameter : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * Complex.I)

theorem cuspParameter_ne_one : cuspParameter ≠ 1 := by
  have hExp : cuspParameter = (Real.exp (-2 * Real.pi) : ℂ) := by
    rw [cuspParameter, Complex.ofReal_exp]
    congr 1
    push_cast
    calc
      2 * (Real.pi : ℂ) * Complex.I * Complex.I =
          2 * (Real.pi : ℂ) * (Complex.I * Complex.I) := by ring
      _ = -2 * (Real.pi : ℂ) := by rw [Complex.I_mul_I]; ring
  intro h
  have hReal : Real.exp (-2 * Real.pi) = 1 := by
    simpa only [hExp, Complex.ofReal_re, Complex.one_re] using congrArg Complex.re h
  exact (Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos])).ne hReal

/-- On actual endomorphisms of the two-dimensional fiber, the scalar and all
unital automorphism versions of the bracket differ at τ = i. -/
theorem paper10_cusp_scalar_twist_incompatible
    (σ : Matrix (Fin 2) (Fin 2) ℂ ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ) :
    scalarBracket cuspParameter ≠ automorphismBracket σ :=
  scalar_bracket_ne_automorphism_bracket cuspParameter cuspParameter_ne_one σ

end

end ManuscriptAudit.ScalarTwistCompatibility

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ScalarTwistCompatibility.scalar_bracket_ne_automorphism_bracket,
      ``ManuscriptAudit.ScalarTwistCompatibility.scalar_bracket_trace_one_nonzero,
      ``ManuscriptAudit.ScalarTwistCompatibility.cuspParameter_ne_one,
      ``ManuscriptAudit.ScalarTwistCompatibility.paper10_cusp_scalar_twist_incompatible] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
