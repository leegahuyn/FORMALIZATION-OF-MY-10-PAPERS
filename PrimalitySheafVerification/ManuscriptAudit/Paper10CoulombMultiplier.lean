import Lean.Util.CollectAxioms
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import PrimalitySheafVerification.ManuscriptAudit.HighInfinityCusp

/-!
# A real bounded multiplier can leave the Coulomb slice

Paper 10, physical pages 494 and 496. The pointwise scalar multiplier and
the one-form below are smooth, supported in the high cusp heights 2–4,
and compatible with the actual level-two orbit relation in that chart.
The printed hyperbolic Hodge stars give a zero codifferential before
multiplication and a nonzero one afterwards.
-/

namespace ManuscriptAudit.Paper10CoulombMultiplier

open LiteralCuspTruncation (orbitPoint)
open scoped UpperHalfPlane

noncomputable section

abbrev ScalarField := ℝ → ℝ → ℝ
abbrev OneForm := ℝ → ℝ → ℝ × ℝ

/-- The coefficients of the star on one-forms in equation (2.13). -/
def hodgeOne (a : ℝ × ℝ) : ℝ × ℝ := (-a.2, a.1)

/-- The coefficient of the exterior derivative in the dx∧dy direction. -/
def exteriorDerivative (a : OneForm) (x y : ℝ) : ℝ :=
  deriv (fun t => (a t y).2) x - deriv (fun t => (a x t).1) y

/-- On one-forms, the codifferential is minus star, d, star. The last star
multiplies the dx∧dy coefficient by y² in equation (2.13). -/
def codifferential (a : OneForm) (x y : ℝ) : ℝ :=
  -(y ^ 2 * exteriorDerivative (fun s t => hodgeOne (a s t)) x y)

def heightCutoff (y : ℝ) : ℝ :=
  Real.smoothTransition (y - 2) * Real.smoothTransition (4 - y)

def witnessForm : OneForm := fun _ y => (heightCutoff y, 0)

def potential : ScalarField := fun x y => heightCutoff y * Real.sin (Real.pi * x)

def multipliedForm : OneForm := fun x y =>
  (potential x y * (witnessForm x y).1, potential x y * (witnessForm x y).2)

private theorem heightCutoff_smooth : ContDiff ℝ ⊤ heightCutoff := by
  have hFirst : ContDiff ℝ ⊤ (fun y : ℝ => y - 2) := contDiff_id.sub contDiff_const
  have hSecond : ContDiff ℝ ⊤ (fun y : ℝ => 4 - y) := contDiff_const.sub contDiff_id
  change ContDiff ℝ ⊤ (fun y => Real.smoothTransition (y - 2) * Real.smoothTransition (4 - y))
  exact (Real.smoothTransition.contDiff.comp hFirst).mul
    (Real.smoothTransition.contDiff.comp hSecond)

theorem witnessForm_smooth : ContDiff ℝ ⊤ (Function.uncurry witnessForm) := by
  exact (heightCutoff_smooth.comp contDiff_snd).prodMk contDiff_const

theorem potential_smooth : ContDiff ℝ ⊤ (Function.uncurry potential) := by
  have h : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => Real.pi * p.1) := contDiff_const.mul contDiff_fst
  change ContDiff ℝ ⊤ (fun p : ℝ × ℝ => heightCutoff p.2 * Real.sin (Real.pi * p.1))
  exact (heightCutoff_smooth.comp contDiff_snd).mul (Real.contDiff_sin.comp h)

theorem heightCutoff_zero_of_outside {y : ℝ} (hy : y ≤ 2 ∨ 4 ≤ y) : heightCutoff y = 0 := by
  rcases hy with hy | hy
  · rw [heightCutoff, Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hy), zero_mul]
  · rw [heightCutoff, Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hy), mul_zero]

theorem witness_zero_of_outside (x : ℝ) {y : ℝ} (hy : y ≤ 2 ∨ 4 ≤ y) :
    witnessForm x y = 0 ∧ potential x y = 0 := by
  simp [witnessForm, potential, heightCutoff_zero_of_outside hy]

private theorem heightCutoff_at_three : heightCutoff 3 = 1 := by
  have h := Real.smoothTransition.one_of_one_le (x := 1) le_rfl
  norm_num [heightCutoff, h]

private theorem heightCutoff_nonneg (y : ℝ) : 0 ≤ heightCutoff y :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

private theorem heightCutoff_le_one (y : ℝ) : heightCutoff y ≤ 1 := by
  unfold heightCutoff
  simpa using mul_le_mul (Real.smoothTransition.le_one (y - 2))
    (Real.smoothTransition.le_one (4 - y)) (Real.smoothTransition.nonneg (4 - y))
    (zero_le_one : (0 : ℝ) ≤ 1)

theorem potential_bounded (x y : ℝ) : |potential x y| ≤ 1 := by
  rw [potential, abs_mul, abs_of_nonneg (heightCutoff_nonneg y)]
  have hs : |Real.sin (Real.pi * x)| ≤ 1 :=
    abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  simpa using mul_le_mul (heightCutoff_le_one y) hs
    (abs_nonneg (Real.sin (Real.pi * x))) (zero_le_one : (0 : ℝ) ≤ 1)

def fiberInner (y : ℝ) (u v : ℝ × ℝ) : ℝ := y ^ 2 * (u.1 * v.1 + u.2 * v.2)

theorem potential_fiber_symmetric (x y : ℝ) (u v : ℝ × ℝ) :
    fiberInner y (potential x y * u.1, potential x y * u.2) v =
      fiberInner y u (potential x y * v.1, potential x y * v.2) := by
  simp only [fiberInner]
  ring

theorem potential_periodic (x y : ℝ) (m : ℤ) :
    potential (x + 2 * (m : ℝ)) y = potential x y := by
  unfold potential
  rw [show Real.pi * (x + 2 * (m : ℝ)) = Real.pi * x + (m : ℝ) * (2 * Real.pi) by ring,
    Real.sin_add_int_mul_two_pi]

/-- The local coefficients are independent of the high-cusp lift to the
upper half-plane. The transition between two such lifts is a translation. -/
theorem witness_agrees_on_high_orbits {z w : ℍ}
    (hz : 1 < z.im) (hw : 1 < w.im) (h : orbitPoint w = orbitPoint z) :
    witnessForm w.re w.im = witnessForm z.re z.im ∧
      potential w.re w.im = potential z.re z.im := by
  obtain ⟨m, hm⟩ := (HighInfinityCusp.high_orbitPoint_eq_iff_even_translate
    (Y := 1) le_rfl hz hw).mp h
  have hRe : w.re = z.re + 2 * (m : ℝ) := by
    simpa [Complex.add_re, Complex.mul_re] using congrArg Complex.re hm
  have hIm : w.im = z.im := by
    simpa [Complex.add_im, Complex.mul_im] using congrArg Complex.im hm
  rw [hRe, hIm]
  exact ⟨rfl, potential_periodic _ _ _⟩

theorem originalForm_coulomb (x y : ℝ) : codifferential witnessForm x y = 0 := by
  simp [codifferential, exteriorDerivative, hodgeOne, witnessForm]

theorem multipliedForm_codifferential_at_witness :
    codifferential multipliedForm 0 3 = -(9 * Real.pi) := by
  have hs : HasDerivAt (fun x : ℝ => Real.sin (Real.pi * x)) Real.pi 0 := by
    simpa only [Function.comp_apply, mul_zero, Real.cos_zero, one_mul, mul_one] using
      (Real.hasDerivAt_sin (Real.pi * 0)).comp 0
        ((hasDerivAt_id' (0 : ℝ)).const_mul Real.pi)
  have hx : (fun t : ℝ => (hodgeOne (multipliedForm t 3)).2) =
      (fun t : ℝ => Real.sin (Real.pi * t)) := by
    funext t
    simp [hodgeOne, multipliedForm, witnessForm, potential, heightCutoff_at_three]
  have hy : (fun t : ℝ => (hodgeOne (multipliedForm 0 t)).1) = (fun _ : ℝ => 0) := by
    funext t
    simp [hodgeOne, multipliedForm, witnessForm]
  rw [codifferential, exteriorDerivative, hx, hy, hs.deriv, deriv_const, sub_zero]
  norm_num

theorem bounded_real_potential_does_not_preserve_coulomb :
    (∀ x y, |potential x y| ≤ 1) ∧
      (∀ x y, codifferential witnessForm x y = 0) ∧
      codifferential multipliedForm 0 3 ≠ 0 := by
  refine ⟨potential_bounded, originalForm_coulomb, ?_⟩
  rw [multipliedForm_codifferential_at_witness]
  exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) Real.pi_pos.ne')

end

end ManuscriptAudit.Paper10CoulombMultiplier

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper10CoulombMultiplier.witnessForm_smooth,
      ``ManuscriptAudit.Paper10CoulombMultiplier.potential_smooth,
      ``ManuscriptAudit.Paper10CoulombMultiplier.witness_zero_of_outside,
      ``ManuscriptAudit.Paper10CoulombMultiplier.potential_bounded,
      ``ManuscriptAudit.Paper10CoulombMultiplier.potential_fiber_symmetric,
      ``ManuscriptAudit.Paper10CoulombMultiplier.witness_agrees_on_high_orbits,
      ``ManuscriptAudit.Paper10CoulombMultiplier.originalForm_coulomb,
      ``ManuscriptAudit.Paper10CoulombMultiplier.multipliedForm_codifferential_at_witness,
      ``ManuscriptAudit.Paper10CoulombMultiplier.bounded_real_potential_does_not_preserve_coulomb] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
