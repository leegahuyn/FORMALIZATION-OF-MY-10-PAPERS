import Lean.Util.CollectAxioms
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum

/-!
# Projected cancellation from a twisted trace

Paper 10, physical PDF pp. 489–490, equations (4.22)–(4.28).
Use the associative degree-zero product and the stated bilinear trace
formula. The general identities apply when the projection fixes the
tested vectors and can be moved across the pairing. The finite example
tests the algebraic inference with the identity projection.
-/

namespace ManuscriptAudit.ProjectedTwistedTrace

section Algebra

variable {A K : Type*} [Ring A] [AddCommGroup K]

def tracePair (T : A →+ K) (u v : A) : K := -T (u * v)

def twistedBracket (σ : A → A) (u v : A) : A := u * v - σ v * u

def projectedBracket (P σ : A → A) (u v : A) : A := P (twistedBracket σ u v)

def TwistedCyclic (T : A →+ K) (σ : A → A) : Prop :=
  ∀ a b, T (a * b) = T (σ b * a)

def PairCompatible (T : A →+ K) (P : A → A) : Prop :=
  ∀ a b, tracePair T (P a) b = tracePair T a (P b)

private theorem twisted_alternating (T : A →+ K) (σ : A → A)
    (hT : TwistedCyclic T σ) (u v w : A) :
    tracePair T (twistedBracket σ u v) w =
      -tracePair T (twistedBracket σ u w) v := by
  unfold tracePair twistedBracket
  rw [sub_mul, sub_mul, map_sub, map_sub, hT (u * v) w, hT (u * w) v,
    mul_assoc (σ v) u w, mul_assoc (σ w) u v]
  abel

/-- The last two variables alternate with the nonlinear output in
the first pairing slot on both sides. -/
theorem projected_alternating (T : A →+ K) (P σ : A → A)
    (hT : TwistedCyclic T σ) (hP : PairCompatible T P)
    (u v w : A) (hv : P v = v) (hw : P w = w) :
    tracePair T (projectedBracket P σ u v) w =
      -tracePair T (projectedBracket P σ u w) v := by
  unfold projectedBracket
  rw [hP _ w, hw, hP _ v, hv]
  exact twisted_alternating T σ hT u v w

/-- The repeated-input cancellation (4.27) follows directly from
twisted cyclicity on the projection-fixed range. -/
theorem projected_diagonal_cancellation (T : A →+ K) (P σ : A → A)
    (hT : TwistedCyclic T σ) (hP : PairCompatible T P)
    (u v : A) (hv : P v = v) :
    tracePair T (projectedBracket P σ u v) v = 0 := by
  unfold projectedBracket
  rw [hP _ v, hv]
  unfold tracePair twistedBracket
  rw [sub_mul, map_sub, hT (u * v) v, mul_assoc (σ v) u v, sub_self, neg_zero]

/-- Equation (4.28) is the quadratic case of (4.27). -/
theorem projected_energy_cancellation (T : A →+ K) (P σ : A → A)
    (hT : TwistedCyclic T σ) (hP : PairCompatible T P)
    (u : A) (hu : P u = u) :
    tracePair T (projectedBracket P σ u u) u = 0 :=
  projected_diagonal_cancellation T P σ hT hP u u hu

/-- The printed right-hand side minus the left-hand side measures precisely
the change in the projected bracket under the trace twist. -/
theorem printed_rhs_defect (T : A →+ K) (P σ : A → A)
    (hT : TwistedCyclic T σ) (hP : PairCompatible T P)
    (u v w : A) (hv : P v = v) (hw : P w = w) :
    -tracePair T v (projectedBracket P σ u w) - tracePair T (projectedBracket P σ u v) w =
      T ((σ (projectedBracket P σ u w) - projectedBracket P σ u w) * v) := by
  rw [projected_alternating T P σ hT hP u v w hv hw]
  unfold tracePair
  rw [sub_mul, map_sub, hT v (projectedBracket P σ u w)]
  abel

/-- Symmetry on the tested vector and the actual bracket output is the
exact additional equality needed for the printed slot order (4.26). -/
theorem printed_skew_iff_output_pair_symmetric (T : A →+ K) (P σ : A → A)
    (hT : TwistedCyclic T σ) (hP : PairCompatible T P)
    (u v w : A) (hv : P v = v) (hw : P w = w) :
    (tracePair T (projectedBracket P σ u v) w =
      -tracePair T v (projectedBracket P σ u w)) ↔
      tracePair T (projectedBracket P σ u w) v =
        tracePair T v (projectedBracket P σ u w) := by
  rw [projected_alternating T P σ hT hP u v w hv hw]
  constructor
  · intro h
    simpa only [neg_neg] using congrArg (fun x : K => -x) h
  · intro h
    rw [h]

end Algebra

section MatrixModel

abbrev Mat₂ := Matrix (Fin 2) (Fin 2) ℂ

private theorem mul_inv_mul {A : Type*} [Ring A] (d : Aˣ) (x : A) :
    (d : A) * ((↑d⁻¹ : A) * x) = x := by
  rw [← mul_assoc, Units.mul_inv, one_mul]

private theorem inv_mul_mul {A : Type*} [Ring A] (d : Aˣ) (x : A) :
    (↑d⁻¹ : A) * ((d : A) * x) = x := by
  rw [← mul_assoc, Units.inv_mul, one_mul]

def innerTwist {A : Type*} [Ring A] (d : Aˣ) : A ≃+* A where
  toFun x := (↑d⁻¹ : A) * x * (d : A)
  invFun x := (d : A) * x * (↑d⁻¹ : A)
  left_inv x := by
    change (d : A) * ((↑d⁻¹ : A) * x * (d : A)) * (↑d⁻¹ : A) = x
    simp only [mul_assoc, Units.mul_inv, mul_one, mul_inv_mul d]
  right_inv x := by
    change (↑d⁻¹ : A) * ((d : A) * x * (↑d⁻¹ : A)) * (d : A) = x
    simp only [mul_assoc, Units.inv_mul, mul_one, inv_mul_mul d]
  map_add' x y := by simp only [mul_add, add_mul]
  map_mul' x y := by simp only [mul_assoc, mul_inv_mul d]

@[simp] theorem innerTwist_apply {A : Type*} [Ring A] (d : Aˣ) (x : A) :
    innerTwist d x = (↑d⁻¹ : A) * x * (d : A) := rfl

def weightedTrace (d : Mat₂ˣ) : Mat₂ →+ ℂ where
  toFun x := Matrix.trace ((d : Mat₂) * x)
  map_zero' := by simp
  map_add' x y := by simp [mul_add]

@[simp] theorem weightedTrace_apply (d : Mat₂ˣ) (x : Mat₂) :
    weightedTrace d x = Matrix.trace ((d : Mat₂) * x) := rfl

theorem weightedTrace_twisted (d : Mat₂ˣ) : TwistedCyclic (weightedTrace d) (innerTwist d) := by
  intro x y
  simp only [weightedTrace_apply, innerTwist_apply]
  rw [Matrix.trace_mul_cycle' (d : Mat₂) x y]
  congr 1
  simp only [mul_assoc, mul_inv_mul d]

open scoped Matrix

def density : Mat₂ˣ :=
  ⟨!![2, 0; 0, 1], !![(1 / 2 : ℂ), 0; 0, 1],
    by
      norm_num [Matrix.mul_fin_two]
      exact (Matrix.one_fin_two (α := ℂ)).symm,
    by
      norm_num [Matrix.mul_fin_two]
      exact (Matrix.one_fin_two (α := ℂ)).symm⟩

def e00 : Mat₂ := !![1, 0; 0, 0]
def e01 : Mat₂ := !![0, 1; 0, 0]
def e10 : Mat₂ := !![0, 0; 1, 0]

theorem matrix_left_value :
    tracePair (weightedTrace density) (projectedBracket id (innerTwist density) e00 e01) e10 =
      -2 := by
  norm_num [tracePair, projectedBracket, twistedBracket, density, e00, e01, e10,
    Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

theorem matrix_printed_right_value :
    -tracePair (weightedTrace density) e01
      (projectedBracket id (innerTwist density) e00 e10) = -4 := by
  norm_num [tracePair, projectedBracket, twistedBracket, density, e00, e01, e10,
    Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

theorem matrix_corrected_right_value :
    -tracePair (weightedTrace density)
      (projectedBracket id (innerTwist density) e00 e10) e01 = -2 := by
  have h := projected_alternating (weightedTrace density) id (innerTwist density)
    (weightedTrace_twisted density) (fun _ _ => rfl) e00 e01 e10 rfl rfl
  exact h.symm.trans matrix_left_value

/-- The displayed weighted matrix trace, ring automorphism and identity
projection satisfy the algebraic hypotheses and refute the printed slot order. -/
theorem matrix_printed_skew_refuted :
    TwistedCyclic (weightedTrace density) (innerTwist density) ∧
    PairCompatible (weightedTrace density) id ∧
    tracePair (weightedTrace density) (projectedBracket id (innerTwist density) e00 e01) e10 ≠
      -tracePair (weightedTrace density) e01
        (projectedBracket id (innerTwist density) e00 e10) := by
  refine ⟨weightedTrace_twisted density, fun _ _ => rfl, ?_⟩
  rw [matrix_left_value, matrix_printed_right_value]
  norm_num

end MatrixModel

end ManuscriptAudit.ProjectedTwistedTrace

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProjectedTwistedTrace.projected_alternating,
      ``ManuscriptAudit.ProjectedTwistedTrace.projected_diagonal_cancellation,
      ``ManuscriptAudit.ProjectedTwistedTrace.projected_energy_cancellation,
      ``ManuscriptAudit.ProjectedTwistedTrace.printed_rhs_defect,
      ``ManuscriptAudit.ProjectedTwistedTrace.printed_skew_iff_output_pair_symmetric,
      ``ManuscriptAudit.ProjectedTwistedTrace.matrix_corrected_right_value,
      ``ManuscriptAudit.ProjectedTwistedTrace.matrix_printed_skew_refuted] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
