import Lean.Util.CollectAxioms
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import PrimalitySheafVerification.ManuscriptAudit.SmoothGaugeCurvature

/-!
# Flat transport need not preserve norm or growth

The argument on physical p. 446 attributes norm and exponent
preservation to flatness. On a trivial complex line the smooth
connection d+dx is flat while the parallel section exp(-x) has
strictly changing norm and logarithmic slope -1.
-/

namespace ManuscriptAudit.Paper9FlatTransportNorm

open SmoothGaugeCurvature (Field2 partialX partialY curvature)

noncomputable section

def connectionX : Field2 ℂ := fun _ _ => 1
def connectionY : Field2 ℂ := fun _ _ => 0

def parallelField (x _ : ℝ) : ℂ := (Real.exp (-x) : ℝ)

def covariantX (f : Field2 ℂ) (x y : ℝ) : ℂ :=
  partialX f x y + connectionX x y * f x y

def covariantY (f : Field2 ℂ) (x y : ℝ) : ℂ :=
  partialY f x y + connectionY x y * f x y

theorem curvature_zero (x y : ℝ) : curvature connectionX connectionY x y = 0 := by
  simp [curvature, partialX, partialY, connectionX, connectionY]
  change deriv (fun _ : ℝ => (1 : ℂ)) y = 0
  exact deriv_const y _

private theorem exponential_hasDeriv (x : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-x)) x := by
  simpa using ((hasDerivAt_id x).neg.exp)

theorem section_parallel (x y : ℝ) : covariantX parallelField x y = 0 ∧ covariantY parallelField x y = 0 := by
  have hx : deriv (fun s => parallelField s y) x = ((-Real.exp (-x) : ℝ) : ℂ) :=
    (exponential_hasDeriv x).ofReal_comp.deriv
  constructor
  · rw [covariantX, partialX, hx, connectionX, one_mul, parallelField, Complex.ofReal_neg]
    exact neg_add_cancel _
  · simp [covariantY, partialY, parallelField, connectionY]
    change deriv (fun _ : ℝ => ((Real.exp (-x) : ℝ) : ℂ)) y = 0
    exact deriv_const y _

theorem section_norm (x y : ℝ) : ‖parallelField x y‖ = Real.exp (-x) := by
  rw [parallelField, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]

theorem section_norm_strictly_decreases {x₁ x₂ : ℝ} (h : x₁ < x₂) (y : ℝ) :
    ‖parallelField x₂ y‖ < ‖parallelField x₁ y‖ := by
  rw [section_norm, section_norm]
  exact Real.exp_lt_exp.mpr (neg_lt_neg h)

theorem logarithmic_norm_slope (x y : ℝ) :
    deriv (fun s => Real.log ‖parallelField s y‖) x = -1 := by
  have h : (fun s => Real.log ‖parallelField s y‖) = fun s : ℝ => -s := by
    funext s
    rw [section_norm, Real.log_exp]
  rw [h]
  exact ((hasDerivAt_id x).neg).deriv

/-- Flat rank-one transport along a segment can lower the usual fibre norm. -/
theorem native_flat_nonisometric_transport :
    (∀ x y, curvature connectionX connectionY x y = 0) ∧
    (∀ x y, covariantX parallelField x y = 0 ∧ covariantY parallelField x y = 0) ∧
    ‖parallelField 1 0‖ < ‖parallelField 0 0‖ :=
  ⟨curvature_zero, section_parallel, section_norm_strictly_decreases zero_lt_one 0⟩

end
end ManuscriptAudit.Paper9FlatTransportNorm

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper9FlatTransportNorm.curvature_zero,
      ``ManuscriptAudit.Paper9FlatTransportNorm.section_parallel,
      ``ManuscriptAudit.Paper9FlatTransportNorm.section_norm_strictly_decreases,
      ``ManuscriptAudit.Paper9FlatTransportNorm.logarithmic_norm_slope,
      ``ManuscriptAudit.Paper9FlatTransportNorm.native_flat_nonisometric_transport] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
