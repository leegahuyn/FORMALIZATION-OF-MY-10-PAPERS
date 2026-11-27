import Lean.Util.CollectAxioms
import Mathlib.Analysis.Calculus.MeanValue
import PrimalitySheafVerification.ManuscriptAudit.Paper10CoulombProductRule

/-! A smooth partition on the width-two cusp can send a Coulomb variation outside the Coulomb slice. -/

namespace ManuscriptAudit.Paper10CoulombPartition

open Paper10CoulombMultiplier Paper10CoulombProductRule
open scoped ContDiff BigOperators

noncomputable section

set_option backward.isDefEq.respectTransparency false

def first : ScalarField := fun x y => (heightCutoff y + potential x y) / 2

def second : ScalarField := fun x y => 1 - first x y

theorem partition_properties (x y : ℝ) :
    0 ≤ first x y ∧ 0 ≤ second x y ∧ first x y + second x y = 1 := by
  have h₀ : 0 ≤ heightCutoff y :=
    mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  have h₁ : heightCutoff y ≤ 1 := by
    unfold heightCutoff
    simpa using mul_le_mul (Real.smoothTransition.le_one (y - 2))
      (Real.smoothTransition.le_one (4 - y)) (Real.smoothTransition.nonneg (4 - y))
      (zero_le_one : (0 : ℝ) ≤ 1)
  have hs₀ : 0 ≤ 1 + Real.sin (Real.pi*x) := by linarith [Real.neg_one_le_sin (Real.pi*x)]
  have hs₁ : 1 + Real.sin (Real.pi*x) ≤ 2 := by linarith [Real.sin_le_one (Real.pi*x)]
  have hm₀ := mul_nonneg h₀ hs₀
  have hm₁ := mul_le_mul_of_nonneg_left hs₁ h₀
  refine ⟨?_, ?_, ?_⟩
  · unfold first potential
    nlinarith only [hm₀]
  · unfold second first potential
    nlinarith only [hm₁, h₁]
  · unfold second
    ring

theorem partition_smooth :
    ContDiff ℝ ∞ (Function.uncurry first) ∧ ContDiff ℝ ∞ (Function.uncurry second) := by
  have hHeight : ContDiff ℝ ∞ (fun p : ℝ×ℝ => heightCutoff p.2) := by
    simpa only [Function.uncurry, witnessForm] using witnessForm_smooth.fst
  have hPot : ContDiff ℝ ∞ (fun p : ℝ×ℝ => potential p.1 p.2) := potential_smooth
  have hSum : ContDiff ℝ ∞ (fun p : ℝ×ℝ => heightCutoff p.2 + potential p.1 p.2) :=
    hHeight.add hPot
  have hFirst : ContDiff ℝ ∞ (Function.uncurry first) := by
    change ContDiff ℝ ∞ (fun p : ℝ×ℝ => (heightCutoff p.2 + potential p.1 p.2) / 2)
    simpa only [div_eq_mul_inv] using
      hSum.mul (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ×ℝ => (2 : ℝ)⁻¹))
  refine ⟨hFirst, ?_⟩
  change ContDiff ℝ ∞ (fun p : ℝ×ℝ => 1 - first p.1 p.2)
  exact (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ×ℝ => (1 : ℝ))).sub hFirst

theorem partition_periodic (x y : ℝ) (m : ℤ) :
    first (x+2*(m : ℝ)) y = first x y ∧ second (x+2*(m : ℝ)) y = second x y := by
  simp only [second, first, potential_periodic, and_self]

theorem first_zero_off_height_band (x y : ℝ) (hy : y ≤ 2 ∨ 4 ≤ y) : first x y = 0 := by
  simp [first, potential, heightCutoff_zero_of_outside hy]

theorem partition_pieces_not_coulomb :
    (∀ x y, codifferential witnessForm x y = 0) ∧
    codifferential (scaleOneForm first witnessForm) 0 3 = -(9*Real.pi/2) ∧
    codifferential (scaleOneForm second witnessForm) 0 3 = 9*Real.pi/2 := by
  have hHeight : heightCutoff 3 = 1 := by
    have h := Real.smoothTransition.one_of_one_le (x := 1) le_rfl
    norm_num [heightCutoff, h]
  have hPi : HasDerivAt (fun x : ℝ => Real.pi*x) Real.pi 0 := by
    simpa only [mul_one] using (hasDerivAt_id' (0 : ℝ)).const_mul Real.pi
  have hSin : HasDerivAt (fun x : ℝ => Real.sin (Real.pi*x)) Real.pi 0 := by
    simpa only [mul_zero, Real.cos_zero, one_mul] using hPi.sin
  have hFirst : HasDerivAt (fun t : ℝ => (1+Real.sin (Real.pi*t))/2) (Real.pi/2) 0 := by
    simpa only [zero_add, Pi.add_apply] using ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).add hSin).div_const 2
  have hSecond : HasDerivAt (fun t : ℝ => 1-(1+Real.sin (Real.pi*t))/2) (-(Real.pi/2)) 0 := by
    exact hFirst.const_sub 1
  have hf : (fun t : ℝ => (scaleOneForm first witnessForm t 3).1) =
      fun t => (1+Real.sin (Real.pi*t))/2 := by
    funext t
    simp [scaleOneForm, witnessForm, first, potential, hHeight]
  have hs : (fun t : ℝ => (scaleOneForm second witnessForm t 3).1) =
      fun t => 1-(1+Real.sin (Real.pi*t))/2 := by
    funext t
    simp [scaleOneForm, witnessForm, second, first, potential, hHeight]
  refine ⟨originalForm_coulomb, ?_, ?_⟩
  · rw [codifferential_eq_coordinateDivergence, hf, hFirst.deriv]
    simp only [scaleOneForm, witnessForm, mul_zero, deriv_const, add_zero]
    ring
  · rw [codifferential_eq_coordinateDivergence, hs, hSecond.deriv]
    simp only [scaleOneForm, witnessForm, mul_zero, deriv_const, add_zero]
    ring


/-- If every localizer misses a point of the supporting horizontal circle,
no choice of a finite differentiable partition can keep all its pieces co-closed. -/
theorem some_partition_piece_leaves_slice {ι : Type*} [Fintype ι]
    (χ : ι → ScalarField) (hDiff : ∀ i, Differentiable ℝ (fun x => χ i x 3))
    (hMiss : ∀ i, ∃ x, χ i x 3 = 0) (hSum : ∀ x, ∑ i, χ i x 3 = 1) :
    ∃ i x, codifferential (scaleOneForm (χ i) witnessForm) x 3 ≠ 0 := by
  classical
  by_contra! h
  have hHeight : heightCutoff 3 = 1 := by
    have hone := Real.smoothTransition.one_of_one_le (x := 1) le_rfl
    norm_num [heightCutoff, hone]
  have hd (i : ι) (x : ℝ) : deriv (fun t => χ i t 3) x = 0 := by
    have hz := h i x
    rw [codifferential_eq_coordinateDivergence] at hz
    simp only [scaleOneForm, witnessForm, hHeight, mul_one, mul_zero, deriv_const, add_zero] at hz
    linarith
  have hZero (i : ι) (x : ℝ) : χ i x 3 = 0 := by
    obtain ⟨y, hy⟩ := hMiss i
    exact (is_const_of_deriv_eq_zero (hDiff i) (hd i) x y).trans hy
  have hOne := hSum 0
  simp only [hZero, Finset.sum_const_zero, zero_ne_one] at hOne

end
end ManuscriptAudit.Paper10CoulombPartition

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.Paper10CoulombPartition.partition_properties,
      ``ManuscriptAudit.Paper10CoulombPartition.partition_smooth,
      ``ManuscriptAudit.Paper10CoulombPartition.partition_periodic,
      ``ManuscriptAudit.Paper10CoulombPartition.first_zero_off_height_band,
      ``ManuscriptAudit.Paper10CoulombPartition.partition_pieces_not_coulomb,
      ``ManuscriptAudit.Paper10CoulombPartition.some_partition_piece_leaves_slice] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
