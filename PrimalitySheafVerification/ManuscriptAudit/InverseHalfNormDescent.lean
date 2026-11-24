import Lean.Util.CollectAxioms
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Paper 9, physical PDF p. 401, Definition 1. A section with the stated
weight −1/2 automorphy and unit-modulus multipliers is zero if its pointwise
unweighted squared norm descends to the quotient by Γ(2).
-/

namespace ManuscriptAudit.InverseHalfNormDescent

open UpperHalfPlane

open scoped MatrixGroups

noncomputable section

private def shear (c : ℤ) : SL(2, ℤ) :=
  ⟨!![1, 0; c, 1], by simp [Matrix.det_fin_two_of]⟩

private theorem shear_mem (c : ℤ) (hc : (c : ZMod 2) = 0) :
    shear c ∈ CongruenceSubgroup.Gamma 2 := by
  rw [CongruenceSubgroup.Gamma_mem]
  change ((1 : ℤ) : ZMod 2) = 1 ∧ ((0 : ℤ) : ZMod 2) = 0 ∧
    (c : ZMod 2) = 0 ∧ ((1 : ℤ) : ZMod 2) = 1
  simp [hc]

private theorem denom_shear (c : ℤ) (τ : UpperHalfPlane) :
    denom (shear c) τ = (c : ℂ) * (τ : ℂ) + 1 := by
  calc
    _ = (((shear c) 1 0 : ℤ) : ℂ) * (τ : ℂ) + (((shear c) 1 1 : ℤ) : ℂ) :=
      ModularGroup.denom_apply (shear c) τ
    _ = _ := by
      change (c : ℂ) * (τ : ℂ) + ((1 : ℤ) : ℂ) = _
      simp

/-- The squared norm of the printed half-power factor. -/
theorem inverseHalf_norm_sq (z : ℂ) :
    ‖z ^ ((-(1 / 2 : ℝ)) : ℂ)‖ ^ (2 : ℕ) = ‖z‖⁻¹ := by
  have hnorm : ‖z ^ (-((1 / 2 : ℝ) : ℂ))‖ = ‖z‖ ^ (-(1 / 2 : ℝ)) := by
    simpa only [Complex.ofReal_neg] using Complex.norm_cpow_real z (-(1 / 2 : ℝ))
  calc
    _ = (‖z‖ ^ (-(1 / 2 : ℝ))) ^ (2 : ℕ) :=
      congrArg (fun r : ℝ => r ^ (2 : ℕ)) hnorm
    _ = (‖z‖ ^ (-(1 / 2 : ℝ))) ^ ((2 : ℕ) : ℝ) := (Real.rpow_natCast _ 2).symm
    _ = ‖z‖ ^ ((-(1 / 2 : ℝ)) * ((2 : ℕ) : ℝ)) :=
      (Real.rpow_mul (norm_nonneg z) _ _).symm
    _ = _ := by
      have h : (-(1 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = -1 := by norm_num
      rw [h, Real.rpow_neg_one]

private theorem shear_normSq_sum (z : ℂ) :
    Complex.normSq ((2 : ℂ) * z + 1) + Complex.normSq ((-2 : ℂ) * z + 1) =
      2 + 8 * Complex.normSq z := by
  norm_num [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.neg_re, Complex.neg_im] <;> ring

/-- For the actual Γ(2) action, an inverse-half-weight section with unit-modulus
multipliers and invariant unweighted squared norm vanishes pointwise. -/
theorem section_eq_zero_of_inverseHalf_norm_descends
    (u : UpperHalfPlane → ℂ) (ν : SL(2, ℤ) → ℂ)
    (hPhase : ∀ γ ∈ CongruenceSubgroup.Gamma 2, ‖ν γ‖ = 1)
    (hAut : ∀ γ ∈ CongruenceSubgroup.Gamma 2, ∀ τ : UpperHalfPlane,
      u (γ • τ) = ν γ * (denom γ τ) ^ ((-(1 / 2 : ℝ)) : ℂ) * u τ)
    (hDesc : ∀ γ ∈ CongruenceSubgroup.Gamma 2, ∀ τ : UpperHalfPlane,
      ‖u (γ • τ)‖ ^ (2 : ℕ) = ‖u τ‖ ^ (2 : ℕ)) : u = 0 := by
  funext τ
  change u τ = 0
  by_contra hne
  have hpos : 0 < ‖u τ‖ ^ (2 : ℕ) := pow_pos (norm_pos_iff.mpr hne) 2
  have hden (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma 2) :
      ‖denom γ τ‖ = 1 := by
    have hscaled : ‖u (γ • τ)‖ ^ (2 : ℕ) =
        ‖denom γ τ‖⁻¹ * ‖u τ‖ ^ (2 : ℕ) := by
      rw [hAut γ hγ τ, norm_mul, norm_mul, hPhase γ hγ, one_mul, mul_pow,
        inverseHalf_norm_sq]
    have he : ‖denom γ τ‖⁻¹ = 1 := by
      apply mul_right_cancel₀ hpos.ne'
      rw [one_mul, ← hscaled, hDesc γ hγ τ]
    simpa only [inv_inv, inv_one] using congrArg (fun x : ℝ => x⁻¹) he
  have hPlus := hden (shear 2) (shear_mem 2 (by decide))
  have hMinus := hden (shear (-2)) (shear_mem (-2) (by decide))
  have hPlus' : ‖(2 : ℂ) * (τ : ℂ) + 1‖ = 1 := by
    simpa only [denom_shear, Int.cast_ofNat] using hPlus
  have hMinus' : ‖(-2 : ℂ) * (τ : ℂ) + 1‖ = 1 := by
    simpa only [denom_shear, Int.cast_neg, Int.cast_ofNat] using hMinus
  have hSum := shear_normSq_sum (τ : ℂ)
  rw [← Complex.sq_norm ((2 : ℂ) * (τ : ℂ) + 1),
    ← Complex.sq_norm ((-2 : ℂ) * (τ : ℂ) + 1), hPlus', hMinus'] at hSum
  have hτ : 0 < Complex.normSq (τ : ℂ) := UpperHalfPlane.normSq_pos τ
  linarith

end

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``inverseHalf_norm_sq, ``section_eq_zero_of_inverseHalf_norm_descends] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"

end ManuscriptAudit.InverseHalfNormDescent
