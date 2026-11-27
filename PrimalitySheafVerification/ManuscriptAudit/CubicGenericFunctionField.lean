import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.Tactic.LinearCombination

/-! The centered cubic's rational coordinate field and its exact quadratic involution. -/

namespace ManuscriptAudit.CubicGenericFunctionField

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

def radicand (A : K) : RatFunc K := RatFunc.X ^ 3 + RatFunc.C A

theorem radicand_eq_algebraMap (A : K) :
    radicand A = algebraMap K[X] (RatFunc K) (X ^ 3 + C A) := by
  rw [radicand, map_add, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C]

theorem intDegree_radicand (A : K) : (radicand A).intDegree = 3 := by
  rw [radicand_eq_algebraMap, RatFunc.intDegree, RatFunc.num_algebraMap,
    RatFunc.denom_algebraMap, natDegree_add_C, natDegree_X_pow, natDegree_one]
  rfl

theorem square_ne_radicand (A : K) (r : RatFunc K) : r ^ 2 ≠ radicand A := by
  intro h
  by_cases hr : r = 0
  · have h' := congrArg RatFunc.intDegree h
    simp only [hr, zero_pow (by decide : (2 : ℕ) ≠ 0), RatFunc.intDegree_zero,
      intDegree_radicand] at h'
    omega
  · have h' := congrArg RatFunc.intDegree h
    rw [pow_two, RatFunc.intDegree_mul hr hr, intDegree_radicand] at h'
    omega

/-- The degree-two extension K(X,Y), with Y²=X³+A. -/
abbrev Model (A : K) := QuadraticAlgebra (RatFunc K) (radicand A) 0

instance no_root (A : K) : Fact (∀ r : RatFunc K,
    r ^ 2 ≠ radicand A + (0 : RatFunc K) * r) :=
  ⟨fun r => by simpa only [zero_mul, add_zero] using square_ne_radicand A r⟩

/-- The actual generic abscissa. -/
def genericX (A : K) : Model A := algebraMap (RatFunc K) (Model A) RatFunc.X

/-- The actual generic ordinate. -/
def genericY (A : K) : Model A := QuadraticAlgebra.omega

theorem generic_equation (A : K) :
    genericY A ^ 2 = genericX A ^ 3 + algebraMap K (Model A) A := by
  have h : genericY A ^ 2 = algebraMap (RatFunc K) (Model A) (radicand A) := by
    rw [genericY, pow_two, QuadraticAlgebra.omega_mul_omega_eq_mk]
    rfl
  calc
    genericY A ^ 2 = algebraMap (RatFunc K) (Model A) (radicand A) := h
    _ = algebraMap (RatFunc K) (Model A) (RatFunc.X ^ 3 + RatFunc.C A) := rfl
    _ = _ := by
      simp only [map_add, map_pow]
      rfl

/-- The quadratic involution fixes K(X) and changes the sign of Y. -/
def conjugation (A : K) : Model A →ₐ[RatFunc K] Model A where
  toRingHom := starRingEnd (Model A)
  commutes' c := by
    change star (algebraMap (RatFunc K) (Model A) c) = algebraMap (RatFunc K) (Model A) c
    apply QuadraticAlgebra.ext <;> simp

theorem conjugation_genericY (A : K) : conjugation A (genericY A) = -genericY A := by
  change star (genericY A) = -genericY A
  apply QuadraticAlgebra.ext <;> simp [genericY]

/-- A conjugation-fixed element is represented by a literal one-variable rational function. -/
theorem exists_algebraMap_of_fixed {A : K} (h₂ : (2 : RatFunc K) ≠ 0) {z : Model A}
    (hz : conjugation A z = z) : ∃ r : RatFunc K, algebraMap (RatFunc K) (Model A) r = z := by
  have hIm : -z.im = z.im := by
    change star z = z at hz
    simpa only [QuadraticAlgebra.im_star] using congrArg QuadraticAlgebra.im hz
  have hZero : (2 : RatFunc K) * z.im = 0 := by linear_combination -hIm
  have he := (mul_eq_zero.mp hZero).resolve_left h₂
  exact ⟨z.re, QuadraticAlgebra.ext rfl he.symm⟩

end

end ManuscriptAudit.CubicGenericFunctionField

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.CubicGenericFunctionField.intDegree_radicand,
      ``ManuscriptAudit.CubicGenericFunctionField.square_ne_radicand,
      ``ManuscriptAudit.CubicGenericFunctionField.generic_equation,
      ``ManuscriptAudit.CubicGenericFunctionField.conjugation_genericY,
      ``ManuscriptAudit.CubicGenericFunctionField.exists_algebraMap_of_fixed] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
