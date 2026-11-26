import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.HighInfinityCusp

/-!
# The actual q-radius on the upper half-plane and Γ(2) orbits

The complex exponential used in the manuscripts has radius
exp(-2π Im τ). The radius is strictly less than one and changes along
every Γ(2) orbit. Thus the formula gives neither a global quotient
radius nor points in the printed exterior |q|≥1 on this domain.
-/

namespace ManuscriptAudit.ModularQRadius

open UpperHalfPlane LiteralCuspTruncation HighInfinityCusp

noncomputable section

/-- The printed complex exponential on the upper half-plane. -/
def qParameter (z : ℍ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (z : ℂ))

/-- The actual absolute value of the printed complex exponential. -/
def qRadius (z : ℍ) : ℝ := ‖qParameter z‖

theorem qRadius_eq_exp (z : ℍ) : qRadius z = Real.exp (-(2 * Real.pi * z.im)) := by
  unfold qRadius qParameter
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im] <;> ring

theorem qRadius_lt_one (z : ℍ) : qRadius z < 1 := by
  rw [qRadius_eq_exp, ← Real.exp_zero, Real.exp_lt_exp]
  exact neg_lt_zero.mpr (by positivity)

theorem qRadius_lt_of_im_gt {z w : ℍ} (h : w.im < z.im) :
    qRadius z < qRadius w := by
  rw [qRadius_eq_exp, qRadius_eq_exp, Real.exp_lt_exp]
  exact neg_lt_neg (mul_lt_mul_of_pos_left h (by positivity))

theorem exists_same_orbit_strictly_larger_radius (z : ℍ) :
    ∃ w : ℍ, orbitPoint w = orbitPoint z ∧ qRadius z < qRadius w := by
  obtain ⟨g, hg⟩ := exists_smul_im_lt z.im z.im_pos z
  exact ⟨g • z, Quotient.sound ⟨g, rfl⟩, qRadius_lt_of_im_gt hg⟩

/-- The exact q-radius does not factor through the actual Γ(2) quotient. -/
theorem paper9_global_qRadius_refuted :
    ¬ ∃ R : OrbitQuotient → ℝ, ∀ z : ℍ, R (orbitPoint z) = qRadius z := by
  rintro ⟨R, hR⟩
  let z : ℍ := ⟨Complex.I, by simp⟩
  obtain ⟨w, hClass, hlt⟩ := exists_same_orbit_strictly_larger_radius z
  rw [← hR z, ← hR w, hClass] at hlt
  exact (lt_irrefl _ hlt)

/-- The printed exterior has no point of the actual upper half-plane. -/
theorem printed_exterior_empty : {z : ℍ | 1 ≤ qRadius z} = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun z hz => ?_
  exact (not_le.mpr (qRadius_lt_one z)) hz

/-- The local parameter for the actual translation width of the infinity cusp. -/
def widthTwoParameter (z : ℍ) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * (z : ℂ))

/-- The width-two parameter identifies exactly the high-cusp orbit classes. -/
theorem high_widthTwoParameter_eq_iff {Y : ℝ} (hY : 1 ≤ Y) {z w : ℍ}
    (hz : Y < z.im) (hw : Y < w.im) :
    widthTwoParameter w = widthTwoParameter z ↔ orbitPoint w = orbitPoint z := by
  rw [high_orbitPoint_eq_iff_even_translate hY hz hw]
  unfold widthTwoParameter
  rw [Complex.exp_eq_exp_iff_exists_int]
  let a := (Real.pi : ℂ) * Complex.I
  have hPi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt Real.pi_pos)
  have ha : a ≠ 0 := mul_ne_zero hPi Complex.I_ne_zero
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, mul_left_cancel₀ ha ?_⟩
    calc
      a * (w : ℂ) = a * (z : ℂ) + (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := hm
      _ = a * ((z : ℂ) + 2 * (m : ℂ)) := by dsimp [a]; ring
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    rw [hm]
    ring

/-- The printed parameter is the square of the parameter for translation width two. -/
theorem qParameter_is_square (z : ℍ) :
    qParameter z = widthTwoParameter z ^ 2 := by
  let a := (Real.pi : ℂ) * Complex.I * (z : ℂ)
  have h : 2 * (Real.pi : ℂ) * Complex.I * (z : ℂ) = a + a := by dsimp [a]; ring
  rw [qParameter, widthTwoParameter, h, Complex.exp_add, pow_two]

/-- The printed parameter identifies two distinct high-cusp quotient points. -/
theorem high_qParameter_collision {Y : ℝ} (hY : 1 ≤ Y) (z : ℍ) (hz : Y < z.im) :
    ∃ w : ℍ, Y < w.im ∧ qParameter w = qParameter z ∧ orbitPoint w ≠ orbitPoint z := by
  let w : ℍ := ⟨(z : ℂ) + 1, by simpa [Complex.add_im] using z.im_pos⟩
  have hw : Y < w.im := by simpa [w, Complex.add_im] using hz
  refine ⟨w, hw, ?_, ?_⟩
  · have h : 2 * (Real.pi : ℂ) * Complex.I * (w : ℂ) =
        2 * (Real.pi : ℂ) * Complex.I * (z : ℂ) + 2 * (Real.pi : ℂ) * Complex.I := by
      change 2 * (Real.pi : ℂ) * Complex.I * ((z : ℂ) + 1) = _
      ring
    rw [qParameter, qParameter, h, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  · intro hClass
    obtain ⟨m, hm⟩ := (high_orbitPoint_eq_iff_even_translate hY hz hw).mp hClass
    have hmRe : (z : ℂ).re + 1 = (z : ℂ).re + 2 * (m : ℝ) := by
      simpa [w, Complex.add_re, Complex.mul_re] using congrArg Complex.re hm
    have hmOne : (1 : ℝ) = 2 * (m : ℝ) := by linarith
    have hInt : (1 : ℤ) = 2 * m := by exact_mod_cast hmOne
    omega

end

end ManuscriptAudit.ModularQRadius

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.ModularQRadius.qRadius_eq_exp,
      ``ManuscriptAudit.ModularQRadius.qRadius_lt_one,
      ``ManuscriptAudit.ModularQRadius.exists_same_orbit_strictly_larger_radius,
      ``ManuscriptAudit.ModularQRadius.paper9_global_qRadius_refuted,
      ``ManuscriptAudit.ModularQRadius.printed_exterior_empty,
      ``ManuscriptAudit.ModularQRadius.high_widthTwoParameter_eq_iff,
      ``ManuscriptAudit.ModularQRadius.qParameter_is_square,
      ``ManuscriptAudit.ModularQRadius.high_qParameter_collision] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
