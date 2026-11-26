import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Finsupp.Multiset
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Tactic.Abel

/-!
# Divisors of rational functions on the affine line

A polynomial gives the finitely supported integer cycle of its roots.
The difference of the cycles of the normalized numerator and
denominator is additive under multiplication of rational functions.
Every cycle of rational closed points occurs as such a divisor.
-/

namespace ManuscriptAudit.AffineLineDivisor

open scoped BigOperators

noncomputable section

variable (K : Type*) [Field K]

/-- The finite root cycle of a polynomial with coefficients in the ground field. -/
def rootCycle (p : Polynomial K) : K →₀ ℤ :=
  Finsupp.mapRange (fun n : ℕ => (n : ℤ)) rfl p.roots.toFinsupp

@[simp] theorem rootCycle_one : rootCycle K 1 = 0 := by
  ext a
  simp [rootCycle]

@[simp] theorem rootCycle_C (a : K) : rootCycle K (Polynomial.C a) = 0 := by
  ext b
  simp [rootCycle]

theorem rootCycle_mul {p q : Polynomial K} (h : p * q ≠ 0) :
    rootCycle K (p * q) = rootCycle K p + rootCycle K q := by
  classical
  ext a
  simp [rootCycle, Polynomial.roots_mul h, Multiset.toFinsupp_add]

theorem rootCycle_X_sub_C (a : K) :
    rootCycle K (Polynomial.X - Polynomial.C a) = Finsupp.single a 1 := by
  classical
  unfold rootCycle
  rw [Polynomial.roots_X_sub_C, Multiset.toFinsupp_singleton, Finsupp.mapRange_single] <;> rfl

theorem roots_eq_of_rootCycle_eq {p q : Polynomial K} (h : rootCycle K p = rootCycle K q) :
    p.roots = q.roots := by
  classical
  apply Multiset.toFinsupp.injective
  ext a
  have ha := congrArg (fun f : K →₀ ℤ => f a) h
  change (↑(p.roots.toFinsupp a) : ℤ) = ↑(q.roots.toFinsupp a) at ha
  exact_mod_cast ha

/-- The divisor map from rational function units to finite integral cycles,
written as an additive homomorphism. -/
def divisor : Additive (RatFunc K)ˣ →+ (K →₀ ℤ) where
  toFun x := rootCycle K (RatFunc.num (x.toMul : RatFunc K)) -
    rootCycle K (RatFunc.denom (x.toMul : RatFunc K))
  map_zero' := by
    change rootCycle K (RatFunc.num (1 : RatFunc K)) - rootCycle K (RatFunc.denom (1 : RatFunc K)) = 0
    rw [RatFunc.num_one, RatFunc.denom_one, sub_self]
  map_add' x y := by
    let u : RatFunc K := x.toMul
    let v : RatFunc K := y.toMul
    have hu : u ≠ 0 := x.toMul.ne_zero
    have hv : v ≠ 0 := y.toMul.ne_zero
    have h := congrArg (rootCycle K) (RatFunc.num_denom_mul u v)
    rw [rootCycle_mul K (mul_ne_zero (RatFunc.num_ne_zero (mul_ne_zero hu hv))
      (mul_ne_zero (RatFunc.denom_ne_zero u) (RatFunc.denom_ne_zero v))),
      rootCycle_mul K (mul_ne_zero (RatFunc.denom_ne_zero u) (RatFunc.denom_ne_zero v)),
      rootCycle_mul K (mul_ne_zero (mul_ne_zero (RatFunc.num_ne_zero hu) (RatFunc.num_ne_zero hv))
        (RatFunc.denom_ne_zero (u * v))),
      rootCycle_mul K (mul_ne_zero (RatFunc.num_ne_zero hu) (RatFunc.num_ne_zero hv))] at h
    change rootCycle K (RatFunc.num (u * v)) - rootCycle K (RatFunc.denom (u * v)) =
      (rootCycle K (RatFunc.num u) - rootCycle K (RatFunc.denom u)) +
        (rootCycle K (RatFunc.num v) - rootCycle K (RatFunc.denom v))
    calc
      _ = (rootCycle K (RatFunc.num (u * v)) +
          (rootCycle K (RatFunc.denom u) + rootCycle K (RatFunc.denom v))) -
          (rootCycle K (RatFunc.denom u) + rootCycle K (RatFunc.denom v)) -
          rootCycle K (RatFunc.denom (u * v)) := by abel
      _ = ((rootCycle K (RatFunc.num u) + rootCycle K (RatFunc.num v)) +
          rootCycle K (RatFunc.denom (u * v))) -
          (rootCycle K (RatFunc.denom u) + rootCycle K (RatFunc.denom v)) -
          rootCycle K (RatFunc.denom (u * v)) := by rw [h]
      _ = _ := by abel

/-- The divisor of a nonzero polynomial is its cycle of zeros. -/
theorem divisor_polynomial (p : Polynomial K) (hp : p ≠ 0) :
    divisor K (Additive.ofMul (Units.mk0 (algebraMap (Polynomial K) (RatFunc K) p)
      (RatFunc.algebraMap_ne_zero hp))) = rootCycle K p := by
  change rootCycle K (RatFunc.num (algebraMap (Polynomial K) (RatFunc K) p)) -
      rootCycle K (RatFunc.denom (algebraMap (Polynomial K) (RatFunc K) p)) = _
  rw [RatFunc.num_algebraMap, RatFunc.denom_algebraMap, rootCycle_one, sub_zero]

/-- Every finite integral cycle on the rational points of the affine line
is the divisor of a rational function. -/
theorem divisor_surjective : Function.Surjective (divisor K) := by
  classical
  let l (a : K) := Additive.ofMul (Units.mk0
    (algebraMap (Polynomial K) (RatFunc K) (Polynomial.X - Polynomial.C a))
    (RatFunc.algebraMap_ne_zero (Polynomial.X_sub_C_ne_zero a)))
  have hl (a : K) : divisor K (l a) = Finsupp.single a 1 :=
    (divisor_polynomial K _ (Polynomial.X_sub_C_ne_zero a)).trans (rootCycle_X_sub_C K a)
  intro D
  refine ⟨∑ a ∈ D.support, D a • l a, ?_⟩
  rw [map_sum]
  calc
    _ = ∑ a ∈ D.support, Finsupp.single a (D a) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [map_zsmul, hl]
      ext b
      by_cases h : a = b <;> simp [Finsupp.single_apply, h]
    _ = D := Finsupp.sum_single D

end

end ManuscriptAudit.AffineLineDivisor

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineLineDivisor.divisor,
      ``ManuscriptAudit.AffineLineDivisor.divisor_polynomial,
      ``ManuscriptAudit.AffineLineDivisor.divisor_surjective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
