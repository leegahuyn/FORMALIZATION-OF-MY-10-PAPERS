import Lean.Util.CollectAxioms
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A smooth unitary gauge and the printed local bracket

Paper 10, physical PDF p. 471, Lemma 3.2 and equation (3.15).
Use the usual matrix trace and store the coefficients of a one-form in
the order dx, dy. The scalar interpretation uses `σ_q(Y) = qY`, with
a specialization to the cusp parameter at `τ = i`. The identity-twist
interpretation uses the unital algebra automorphism in Axiom 2.3.
-/

namespace ManuscriptAudit.SmoothGaugeBracket

open Matrix
open scoped Matrix

noncomputable section

abbrev Mat₂ := Matrix (Fin 2) (Fin 2) ℂ

def rotation (y : ℝ) : Mat₂ :=
  !![(Real.cos (y - 1) : ℂ), (Real.sin (y - 1) : ℂ);
    -(Real.sin (y - 1) : ℂ), (Real.cos (y - 1) : ℂ)]

def rotationVelocity (y : ℝ) : Mat₂ :=
  !![-(Real.sin (y - 1) : ℂ), (Real.cos (y - 1) : ℂ);
    -(Real.cos (y - 1) : ℂ), -(Real.sin (y - 1) : ℂ)]

def gauge (_x y : ℝ) : Mat₂ := rotation y

def gaugeDx (x y : ℝ) : Mat₂ :=
  fun i j => deriv (fun t : ℝ => gauge t y i j) x

def gaugeDy (x y : ℝ) : Mat₂ :=
  fun i j => deriv (fun t : ℝ => gauge x t i j) y

/-- Each matrix entry of the rotation is smooth. -/
theorem rotation_entry_smooth (i j : Fin 2) :
    ContDiff ℝ ⊤ (fun t : ℝ => rotation t i j) := by
  have hShift : ContDiff ℝ ⊤ (fun t : ℝ => t - 1) := contDiff_id.sub contDiff_const
  have hc : ContDiff ℝ ⊤ (fun t : ℝ => (Real.cos (t - 1) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Real.contDiff_cos.comp hShift)
  have hs : ContDiff ℝ ⊤ (fun t : ℝ => (Real.sin (t - 1) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Real.contDiff_sin.comp hShift)
  fin_cases i <;> fin_cases j
  · simpa [rotation] using hc
  · simpa [rotation] using hs
  · simpa [rotation] using hs.neg
  · simpa [rotation] using hc

/-- The matrix entries have the actual derivatives displayed in
`rotationVelocity`. -/
theorem rotation_entry_hasDerivAt (y : ℝ) (i j : Fin 2) :
    HasDerivAt (fun t : ℝ => rotation t i j) (rotationVelocity y i j) y := by
  have hShift : HasDerivAt (fun t : ℝ => t - 1) 1 y :=
    (hasDerivAt_id y).sub_const 1
  have hc : HasDerivAt (fun t : ℝ => (Real.cos (t - 1) : ℂ))
      (-(Real.sin (y - 1) : ℂ)) y := by
    simpa only [Function.comp_apply, mul_one, Complex.ofReal_neg] using
      ((Real.hasDerivAt_cos (y - 1)).comp y hShift).ofReal_comp
  have hs : HasDerivAt (fun t : ℝ => (Real.sin (t - 1) : ℂ))
      (Real.cos (y - 1) : ℂ) y := by
    simpa only [Function.comp_apply, mul_one] using
      ((Real.hasDerivAt_sin (y - 1)).comp y hShift).ofReal_comp
  fin_cases i <;> fin_cases j
  · simpa [rotation, rotationVelocity] using hc
  · simpa [rotation, rotationVelocity] using hs
  · change HasDerivAt (-(fun t : ℝ => (Real.sin (t - 1) : ℂ)))
        (-(Real.cos (y - 1) : ℂ)) y
    exact hs.neg
  · simpa [rotation, rotationVelocity] using hc

theorem gaugeDx_eq_zero (x y : ℝ) : gaugeDx x y = 0 := by
  apply Matrix.ext
  intro i j
  simp [gaugeDx, gauge]

theorem gaugeDy_eq_velocity (x y : ℝ) : gaugeDy x y = rotationVelocity y := by
  apply Matrix.ext
  intro i j
  exact (rotation_entry_hasDerivAt y i j).deriv

/-- The rotation is unitary, so the adjoint used in the gauge formula is
its genuine inverse. -/
theorem rotation_unitary (y : ℝ) :
    (rotation y)ᴴ * rotation y = 1 ∧ rotation y * (rotation y)ᴴ = 1 := by
  let c : ℂ := (Real.cos (y - 1) : ℂ)
  let s : ℂ := (Real.sin (y - 1) : ℂ)
  have hRotation : rotation y = !![c, s; -s, c] := rfl
  have hcStar : star c = c := Complex.conj_ofReal _
  have hsStar : star s = s := Complex.conj_ofReal _
  have hTranspose : (rotation y)ᴴ = (rotation y)ᵀ := by
    rw [hRotation]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j
    · change star c = c
      exact hcStar
    · change star (-s) = -s
      rw [star_neg, hsStar]
    · change star s = s
      exact hsStar
    · change star c = c
      exact hcStar
  have hTrig : s ^ 2 + c ^ 2 = 1 := by
    simpa only [Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_one] using
      congrArg Complex.ofReal (Real.sin_sq_add_cos_sq (y - 1))
  rw [hTranspose, hRotation]
  constructor <;> apply Matrix.ext <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.transpose_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply] <;> first | linear_combination hTrig | ring

/-- The usual trace meets the conjugation rule of the manuscript for this gauge. -/
theorem trace_conjugation (x y : ℝ) (Z : Mat₂) :
    Matrix.trace ((gauge x y)ᴴ * Z * gauge x y) = Matrix.trace Z := by
  calc
    _ = Matrix.trace (gauge x y * ((gauge x y)ᴴ * Z)) := Matrix.trace_mul_comm _ _
    _ = _ := by
      have hG : gauge x y * (gauge x y)ᴴ = 1 := (rotation_unitary y).2
      rw [← mul_assoc, hG, one_mul]

def wedgeCoefficient (A B : Mat₂ × Mat₂) : Mat₂ := A.1 * B.2 - A.2 * B.1

/-- The ungraded dx∧dy bracket in (3.15) with the scalar interpretation
`σ_q(Y) = qY`. -/
def printedScalarBracket (q : ℂ) (A B : Mat₂ × Mat₂) : Mat₂ :=
  wedgeCoefficient A B - wedgeCoefficient (q • B.1, q • B.2) A

private theorem printedScalarBracket_eq (q : ℂ) (A B : Mat₂ × Mat₂) :
    printedScalarBracket q A B = wedgeCoefficient A B - q • wedgeCoefficient B A := by
  simp only [printedScalarBracket, wedgeCoefficient, Matrix.smul_mul, smul_sub]

/-- The ungraded bracket in (3.15) for the identity twist of Axiom 2.3. -/
def printedBracket (A B : Mat₂ × Mat₂) : Mat₂ :=
  wedgeCoefficient A B - wedgeCoefficient B A

/-- The printed affine gauge law, applied to both coefficient directions. -/
def affineGauge (x y : ℝ) (A : Mat₂ × Mat₂) : Mat₂ × Mat₂ :=
  let g := gauge x y
  (gᴴ * A.1 * g + gᴴ * gaugeDx x y, gᴴ * A.2 * g + gᴴ * gaugeDy x y)

def X : Mat₂ := !![Complex.I, 0; 0, 0]

def Y : Mat₂ := !![0, 1; -1, 0]

private theorem gauge_at_one (x : ℝ) : gauge x 1 = 1 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [gauge, rotation, Matrix.one_apply]

private theorem gaugeDy_at_one (x : ℝ) : gaugeDy x 1 = Y := by
  rw [gaugeDy_eq_velocity]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [rotationVelocity, Y]

private theorem affineGauge_at_one (A : Mat₂ × Mat₂) :
    affineGauge 0 1 A = (A.1, A.2 + Y) := by
  simp [affineGauge, gauge_at_one, gaugeDx_eq_zero, gaugeDy_at_one]

/-- The transformed scalar bracket at the witness point has off-diagonal
entry i for every q. -/
theorem transformed_scalar_bracket_entry (q : ℂ) :
    (printedScalarBracket q (affineGauge 0 1 (X, 0)) (affineGauge 0 1 (0, 0))) 0 1 =
      Complex.I := by
  have hXY : (X * Y) 0 1 = Complex.I := by
    norm_num [X, Y, Matrix.mul_apply, Fin.sum_univ_two]
  have hYX : (Y * X) 0 1 = 0 := by
    norm_num [X, Y, Matrix.mul_apply, Fin.sum_univ_two]
  simp only [printedScalarBracket_eq, affineGauge_at_one, wedgeCoefficient,
    zero_add, zero_mul, mul_zero, sub_zero, zero_sub, smul_neg, sub_neg_eq_add,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    hXY, hYX, mul_zero, add_zero]

/-- The smooth unitary gauge refutes (3.15) under its scalar interpretation
for every central parameter q. -/
theorem smooth_unitary_gauge_refutes_scalar_bracket_covariance (q : ℂ) :
    printedScalarBracket q (affineGauge 0 1 (X, 0)) (affineGauge 0 1 (0, 0)) ≠
      (gauge 0 1)ᴴ * printedScalarBracket q (X, 0) (0, 0) * gauge 0 1 := by
  intro h
  apply Complex.I_ne_zero
  calc
    Complex.I = (printedScalarBracket q
        (affineGauge 0 1 (X, 0)) (affineGauge 0 1 (0, 0))) 0 1 :=
      (transformed_scalar_bracket_entry q).symm
    _ = 0 := by
      rw [h]
      simp only [printedScalarBracket_eq, wedgeCoefficient, mul_zero, zero_mul,
        sub_zero, smul_zero, Matrix.zero_apply]

/-- Scalar covariance fails at the manuscript's cusp parameter
`q = exp(2 π i τ)` evaluated at the witness point `τ = i`. -/
theorem smooth_unitary_gauge_refutes_cusp_scalar_bracket_covariance :
    let q := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * Complex.I)
    printedScalarBracket q (affineGauge 0 1 (X, 0)) (affineGauge 0 1 (0, 0)) ≠
      (gauge 0 1)ᴴ * printedScalarBracket q (X, 0) (0, 0) * gauge 0 1 :=
  smooth_unitary_gauge_refutes_scalar_bracket_covariance
    (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * Complex.I))

/-- A separate instance of the same failure with the identity algebra
automorphism allowed by Axiom 2.3. -/
theorem smooth_unitary_gauge_refutes_bracket_covariance :
    printedBracket (affineGauge 0 1 (X, 0)) (affineGauge 0 1 (0, 0)) ≠
      (gauge 0 1)ᴴ * printedBracket (X, 0) (0, 0) * gauge 0 1 := by
  simpa only [printedScalarBracket_eq, one_smul, printedBracket] using
    smooth_unitary_gauge_refutes_scalar_bracket_covariance 1

end

end ManuscriptAudit.SmoothGaugeBracket

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.SmoothGaugeBracket.rotation_entry_smooth,
      ``ManuscriptAudit.SmoothGaugeBracket.rotation_entry_hasDerivAt,
      ``ManuscriptAudit.SmoothGaugeBracket.rotation_unitary,
      ``ManuscriptAudit.SmoothGaugeBracket.trace_conjugation,
      ``ManuscriptAudit.SmoothGaugeBracket.transformed_scalar_bracket_entry,
      ``ManuscriptAudit.SmoothGaugeBracket.smooth_unitary_gauge_refutes_scalar_bracket_covariance,
      ``ManuscriptAudit.SmoothGaugeBracket.smooth_unitary_gauge_refutes_cusp_scalar_bracket_covariance,
      ``ManuscriptAudit.SmoothGaugeBracket.smooth_unitary_gauge_refutes_bracket_covariance] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
