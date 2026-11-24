import Lean.Util.CollectAxioms
import Mathlib.Analysis.Complex.RealDeriv
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
Set the central parameter to one, the twist to the identity, and the
trace to the usual matrix trace. For a matrix-valued one-form, store
its coefficients in the order dx, dy.
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
  · simpa [rotation, rotationVelocity] using hs.neg
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
  have hTranspose : (rotation y)ᴴ = (rotation y)ᵀ := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [rotation, Matrix.conjTranspose_apply, Matrix.transpose_apply, Complex.star_def]
  have hTrig : (Real.sin (y - 1) : ℂ) ^ 2 + (Real.cos (y - 1) : ℂ) ^ 2 = 1 := by
    simpa only [Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_one] using
      congrArg Complex.ofReal (Real.sin_sq_add_cos_sq (y - 1))
  rw [hTranspose]
  constructor <;> apply Matrix.ext <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [rotation, Matrix.transpose_apply, Matrix.mul_apply, Fin.sum_univ_two,
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

/-- The ungraded bracket in (3.15), for the identity twist, in the dx∧dy component. -/
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

/-- For the actual smooth local gauge, the transformed bracket has
off-diagonal coefficient i while the conjugated original bracket is
zero. The original fields are the constant one-forms (X,0) and (0,0). -/
theorem smooth_unitary_gauge_refutes_bracket_covariance :
    printedBracket (affineGauge 0 1 (X, 0)) (affineGauge 0 1 (0, 0)) ≠
      (gauge 0 1)ᴴ * printedBracket (X, 0) (0, 0) * gauge 0 1 := by
  simp only [affineGauge_at_one, zero_add, printedBracket, wedgeCoefficient, Prod.fst_mk,
    Prod.snd_mk, zero_mul, mul_zero, sub_zero, zero_sub, sub_neg_eq_add]
  intro h
  have hEntry : (X * Y + Y * X) 0 1 = 0 :=
    congrArg (fun M : Mat₂ => M 0 1) h
  have hNonzero : (X * Y + Y * X) 0 1 = Complex.I := by
    norm_num [X, Y, Matrix.mul_apply, Fin.sum_univ_two]
  exact Complex.I_ne_zero (hNonzero.symm.trans hEntry)

end

end ManuscriptAudit.SmoothGaugeBracket

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.SmoothGaugeBracket.rotation_entry_smooth,
      ``ManuscriptAudit.SmoothGaugeBracket.rotation_entry_hasDerivAt,
      ``ManuscriptAudit.SmoothGaugeBracket.rotation_unitary,
      ``ManuscriptAudit.SmoothGaugeBracket.trace_conjugation,
      ``ManuscriptAudit.SmoothGaugeBracket.smooth_unitary_gauge_refutes_bracket_covariance] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
