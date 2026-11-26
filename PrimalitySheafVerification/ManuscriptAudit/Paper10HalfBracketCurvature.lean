import Lean.Util.CollectAxioms
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Exp
import PrimalitySheafVerification.ManuscriptAudit.SmoothGaugeBracket

/-!
# The half-bracket curvature in Paper 10

The product in (2.3) is wedge combined with matrix multiplication.
Under the scalar bracket (2.4), the half-bracket curvature on physical
page 492 has the quadratic term ((1 - q) / 2) times the wedge square.
The local smooth unitary gauge, evaluated at the interior point
(0, 1), distinguishes this formula from (2.6) and violates affine
gauge covariance. We also compute the result if a degree sign is
inserted into the scalar bracket.
-/

namespace ManuscriptAudit.Paper10HalfBracketCurvature

open Matrix
open scoped Matrix
open SmoothGaugeBracket

noncomputable section

abbrev Connection := ℝ → ℝ → Mat₂ × Mat₂

/-- The coefficient of the exterior derivative in the dx∧dy direction. -/
def exteriorDerivative (A : Connection) (x y : ℝ) : Mat₂ :=
  fun i j => deriv (fun s => (A s y).2 i j) x - deriv (fun t => (A x t).1 i j) y

/-- The ordinary curvature used in equation (2.6). -/
def ordinaryCurvature (A : Connection) (x y : ℝ) : Mat₂ :=
  exteriorDerivative A x y + wedgeCoefficient (A x y) (A x y)

/-- The curvature on physical page 492 interpreted using literal (2.4). -/
def literalCurvature (q : ℂ) (A : Connection) (x y : ℝ) : Mat₂ :=
  exteriorDerivative A x y + (1 / 2 : ℂ) • printedScalarBracket q (A x y) (A x y)

/-- The curvature on physical page 492 if the scalar bracket is given
the usual degree sign for two one-forms. -/
def gradedCurvature (q : ℂ) (A : Connection) (x y : ℝ) : Mat₂ :=
  exteriorDerivative A x y + ((1 + q) / 2 : ℂ) • wedgeCoefficient (A x y) (A x y)

theorem literal_bracket_self (q : ℂ) (A : Mat₂ × Mat₂) :
    printedScalarBracket q A A = (1 - q) • wedgeCoefficient A A := by
  calc
    _ = wedgeCoefficient A A - q • wedgeCoefficient A A := by
      simp only [printedScalarBracket, wedgeCoefficient, Matrix.smul_mul, smul_sub]
    _ = _ := by rw [sub_smul, one_smul]

def constantConnection : Connection := fun _ _ => (X, 0)

def transformedConnection : Connection := fun x y => affineGauge x y (constantConnection x y)

private theorem transformed_x_entry (x y : ℝ) :
    (transformedConnection x y).1 0 1 =
      rotation y 0 0 * Complex.I * rotation y 0 1 := by
  have hEntry : (rotation y)ᴴ 0 0 = rotation y 0 0 := by
    change star (rotation y 0 0) = rotation y 0 0
    exact Complex.conj_ofReal (Real.cos (y - 1))
  simp only [transformedConnection, constantConnection, affineGauge, gaugeDx_eq_zero,
    mul_zero, add_zero, gauge]
  simp [X, Matrix.mul_apply, Fin.sum_univ_two, hEntry]

private theorem transformed_x_derivative :
    deriv (fun t => (transformedConnection 0 t).1 0 1) 1 = Complex.I := by
  have hc : HasDerivAt (fun t => rotation t 0 0) 0 1 :=
    (rotation_entry_hasDerivAt 1 0 0).congr_deriv (by norm_num [rotationVelocity])
  have hs : HasDerivAt (fun t => rotation t 0 1) 1 1 :=
    (rotation_entry_hasDerivAt 1 0 1).congr_deriv (by norm_num [rotationVelocity])
  rw [show (fun t => (transformedConnection 0 t).1 0 1) =
    (fun t => rotation t 0 0 * Complex.I * rotation t 0 1) from
      funext (transformed_x_entry 0)]
  have h := ((hc.mul_const Complex.I).mul hs).deriv
  change deriv (fun t => rotation t 0 0 * Complex.I * rotation t 0 1) 1 = _ at h
  simpa [rotation] using h

theorem transformed_exteriorDerivative_entry :
    exteriorDerivative transformedConnection 0 1 0 1 = -Complex.I := by
  have h : (fun t => (transformedConnection t 1).2 0 1) =
      (fun _ : ℝ => ((rotation 1)ᴴ * rotationVelocity 1) 0 1) := by
    funext t
    simp [transformedConnection, constantConnection, affineGauge, gauge, gaugeDy_eq_velocity]
  unfold exteriorDerivative
  rw [h, deriv_const, transformed_x_derivative, zero_sub]

private theorem gauge_at_witness : gauge 0 1 = 1 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [gauge, rotation, Matrix.one_apply]

private theorem gaugeDy_at_witness : gaugeDy 0 1 = Y := by
  rw [gaugeDy_eq_velocity]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [rotationVelocity, Y]

private theorem transformed_at_witness : transformedConnection 0 1 = (X, Y) := by
  simp [transformedConnection, constantConnection, affineGauge, gauge_at_witness,
    gaugeDx_eq_zero, gaugeDy_at_witness]

theorem transformed_wedgeSquare_entry :
    wedgeCoefficient (transformedConnection 0 1) (transformedConnection 0 1) 0 1 =
      Complex.I := by
  rw [transformed_at_witness]
  norm_num [wedgeCoefficient, X, Y, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]

theorem ordinary_transformed_entry :
    ordinaryCurvature transformedConnection 0 1 0 1 = 0 := by
  rw [ordinaryCurvature, Matrix.add_apply, transformed_exteriorDerivative_entry,
    transformed_wedgeSquare_entry, neg_add_cancel]

theorem literal_transformed_entry (q : ℂ) :
    literalCurvature q transformedConnection 0 1 0 1 = (-(1 + q) / 2) * Complex.I := by
  simp only [literalCurvature, Matrix.add_apply, transformed_exteriorDerivative_entry,
    literal_bracket_self, Matrix.smul_apply, smul_eq_mul, transformed_wedgeSquare_entry]
  ring

theorem graded_transformed_entry (q : ℂ) :
    gradedCurvature q transformedConnection 0 1 0 1 = ((q - 1) / 2) * Complex.I := by
  simp only [gradedCurvature, Matrix.add_apply, transformed_exteriorDerivative_entry,
    Matrix.smul_apply, smul_eq_mul, transformed_wedgeSquare_entry]
  ring

private theorem literal_constant (q : ℂ) : literalCurvature q constantConnection 0 1 = 0 := by
  apply Matrix.ext
  intro i j
  simp [literalCurvature, constantConnection, exteriorDerivative, wedgeCoefficient,
    literal_bracket_self]

private theorem graded_constant (q : ℂ) : gradedCurvature q constantConnection 0 1 = 0 := by
  apply Matrix.ext
  intro i j
  simp [gradedCurvature, constantConnection, exteriorDerivative, wedgeCoefficient]

theorem literal_curvature_differs_from_eq26 (q : ℂ) (hq : q ≠ -1) :
    literalCurvature q transformedConnection 0 1 ≠ ordinaryCurvature transformedConnection 0 1 := by
  intro h
  have he := congrArg (fun m : Mat₂ => m 0 1) h
  change literalCurvature q transformedConnection 0 1 0 1 =
    ordinaryCurvature transformedConnection 0 1 0 1 at he
  rw [literal_transformed_entry, ordinary_transformed_entry] at he
  have hz := (mul_eq_zero.mp he).resolve_right Complex.I_ne_zero
  apply hq
  linear_combination -2 * hz

/-- The p. 492 formula with the literal scalar bracket fails (2.8). -/
theorem literal_curvature_not_affine_covariant (q : ℂ) (hq : q ≠ -1) :
    literalCurvature q transformedConnection 0 1 ≠
      (gauge 0 1)ᴴ * literalCurvature q constantConnection 0 1 * gauge 0 1 := by
  rw [literal_constant, mul_zero, zero_mul]
  intro h
  have he := congrArg (fun m : Mat₂ => m 0 1) h
  change literalCurvature q transformedConnection 0 1 0 1 = 0 at he
  rw [literal_transformed_entry] at he
  have hz := (mul_eq_zero.mp he).resolve_right Complex.I_ne_zero
  apply hq
  linear_combination -2 * hz

/-- Inserting the degree sign still gives a failure for every scalar q≠1. -/
theorem graded_curvature_not_affine_covariant (q : ℂ) (hq : q ≠ 1) :
    gradedCurvature q transformedConnection 0 1 ≠
      (gauge 0 1)ᴴ * gradedCurvature q constantConnection 0 1 * gauge 0 1 := by
  rw [graded_constant, mul_zero, zero_mul]
  intro h
  have he := congrArg (fun m : Mat₂ => m 0 1) h
  change gradedCurvature q transformedConnection 0 1 0 1 = 0 at he
  rw [graded_transformed_entry] at he
  have hz := (mul_eq_zero.mp he).resolve_right Complex.I_ne_zero
  apply hq
  linear_combination 2 * hz

/-- The actual cusp parameter at tau = i. -/
def cuspParameter : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * Complex.I)

private theorem cuspParameter_re_bounds : 0 < cuspParameter.re ∧ cuspParameter.re < 1 := by
  have hArg : 2 * (Real.pi : ℂ) * Complex.I * Complex.I =
      ((-2 * Real.pi : ℝ) : ℂ) := by
    rw [mul_assoc (2 * (Real.pi : ℂ)), Complex.I_mul_I]
    push_cast
    ring
  rw [cuspParameter, hArg, ← Complex.ofReal_exp, Complex.ofReal_re]
  exact ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr
    (mul_neg_of_neg_of_pos (by norm_num) Real.pi_pos)⟩

theorem cusp_parameter_curvature_not_affine_covariant :
    literalCurvature cuspParameter transformedConnection 0 1 ≠
      (gauge 0 1)ᴴ * literalCurvature cuspParameter constantConnection 0 1 * gauge 0 1 := by
  apply literal_curvature_not_affine_covariant
  intro h
  have hr := congrArg Complex.re h
  have hp := cuspParameter_re_bounds.1
  rw [hr] at hp
  norm_num at hp

theorem cusp_parameter_graded_curvature_not_affine_covariant :
    gradedCurvature cuspParameter transformedConnection 0 1 ≠
      (gauge 0 1)ᴴ * gradedCurvature cuspParameter constantConnection 0 1 * gauge 0 1 := by
  apply graded_curvature_not_affine_covariant
  intro h
  have hr := congrArg Complex.re h
  have hp := cuspParameter_re_bounds.2
  rw [hr] at hp
  norm_num at hp

/-- In the ungraded bracket convention, the identity automorphism allowed
by Axiom 2.3 has the same local failure with the usual matrix trace. -/
theorem identity_twist_curvature_not_affine_covariant :
    exteriorDerivative transformedConnection 0 1 + (1 / 2 : ℂ) •
        printedBracket (transformedConnection 0 1) (transformedConnection 0 1) ≠
      (gauge 0 1)ᴴ *
        (exteriorDerivative constantConnection 0 1 + (1 / 2 : ℂ) •
          printedBracket (constantConnection 0 1) (constantConnection 0 1)) * gauge 0 1 := by
  simpa [literalCurvature, printedScalarBracket, printedBracket] using
    literal_curvature_not_affine_covariant 1 (by norm_num)

end

end ManuscriptAudit.Paper10HalfBracketCurvature

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper10HalfBracketCurvature.literal_bracket_self,
      ``ManuscriptAudit.Paper10HalfBracketCurvature.transformed_exteriorDerivative_entry,
      ``ManuscriptAudit.Paper10HalfBracketCurvature.transformed_wedgeSquare_entry,
      ``ManuscriptAudit.Paper10HalfBracketCurvature.ordinary_transformed_entry,
      ``ManuscriptAudit.Paper10HalfBracketCurvature.literal_transformed_entry,
      ``ManuscriptAudit.Paper10HalfBracketCurvature.graded_transformed_entry,
      ``ManuscriptAudit.Paper10HalfBracketCurvature.literal_curvature_differs_from_eq26,
      ``ManuscriptAudit.Paper10HalfBracketCurvature.literal_curvature_not_affine_covariant,
      ``ManuscriptAudit.Paper10HalfBracketCurvature.graded_curvature_not_affine_covariant,
      ``ManuscriptAudit.Paper10HalfBracketCurvature.cusp_parameter_curvature_not_affine_covariant,
      ``ManuscriptAudit.Paper10HalfBracketCurvature.cusp_parameter_graded_curvature_not_affine_covariant,
      ``ManuscriptAudit.Paper10HalfBracketCurvature.identity_twist_curvature_not_affine_covariant] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
