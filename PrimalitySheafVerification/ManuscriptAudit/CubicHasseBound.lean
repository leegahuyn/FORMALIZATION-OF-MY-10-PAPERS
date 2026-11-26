import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Tactic.NormNum
import PrimalitySheafVerification.ManuscriptAudit.CubicCharacterMultiplicity
import PrimalitySheafVerification.ManuscriptAudit.CubicTrace

/-! The actual Hasse bound for the good reduced family y² = x³ + A. -/

namespace ManuscriptAudit.CubicHasseBound

open CubicJacobiBound CubicCharacterMultiplicity FiniteFieldPointCount
open scoped BigOperators

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private theorem quadraticComplex_ne_one (hF : ringChar F ≠ 2) :
    (quadraticComplex : MulChar F ℂ) ≠ 1 := by
  intro h
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one hF
  have ha₀ : a ≠ 0 := by
    intro h₀
    subst a
    rw [quadraticChar_zero] at ha
    exact (by decide : (0 : ℤ) ≠ -1) ha
  have e := congrArg (fun χ : MulChar F ℂ => χ a) h
  change (quadraticChar F a : ℂ) = (1 : MulChar F ℂ) a at e
  rw [ha, MulChar.one_apply ha₀.isUnit] at e
  norm_num at e

private theorem quadraticComplex_sq :
    (quadraticComplex : MulChar F ℂ) ^ 2 = 1 := by
  apply MulChar.ext
  intro u
  rw [MulChar.pow_apply_coe, MulChar.one_apply_coe]
  change (quadraticChar F (u : F) : ℂ) ^ 2 = 1
  exact_mod_cast (quadraticChar_sq_one u.ne_zero)

private theorem ne_one_of_orderThree_pow {χ : MulChar F ℂ} (hχ : orderOf χ = 3)
    {n : ℕ} (hn : ¬ 3 ∣ n) : χ ^ n ≠ 1 := by
  intro h
  have h' := orderOf_dvd_of_pow_eq_one h
  rw [hχ] at h'
  exact hn h'

private theorem mul_quadratic_eq_one {χ : MulChar F ℂ} (h : χ * quadraticComplex = 1) :
    χ = quadraticComplex := by
  calc
    χ = χ * 1 := (mul_one _).symm
    _ = χ * (quadraticComplex * quadraticComplex) := by rw [← pow_two, quadraticComplex_sq]
    _ = quadraticComplex := by rw [← mul_assoc, h, one_mul]

private theorem trace_bound_of_orderThree (hF : ringChar F ≠ 2)
    (hdiv : 3 ∣ Fintype.card F - 1) {A : F} (hA : A ≠ 0) :
    ‖cubicTraceSum A‖ ≤ 2 * Real.sqrt (Fintype.card F : ℝ) := by
  obtain ⟨χ, hχ⟩ := exists_orderThree_character hdiv
  have hχ₁ : χ ≠ 1 := by
    simpa only [pow_one] using ne_one_of_orderThree_pow hχ (by decide : ¬ 3 ∣ (1 : ℕ))
  have hχ₂ := ne_one_of_orderThree_pow hχ (by decide : ¬ 3 ∣ (2 : ℕ))
  have hχ₄ := ne_one_of_orderThree_pow hχ (by decide : ¬ 3 ∣ (4 : ℕ))
  have hχφ : χ * quadraticComplex ≠ 1 := by
    intro h
    exact hχ₂ (by rw [mul_quadratic_eq_one h, quadraticComplex_sq])
  have hχ₂φ : χ ^ 2 * quadraticComplex ≠ 1 := by
    intro h
    exact hχ₄ (by
      change χ ^ (2 * 2 : ℕ) = 1
      rw [pow_mul, mul_quadratic_eq_one h, quadraticComplex_sq])
  have hchar : ringChar ℂ ≠ ringChar F := by
    rw [ringChar.eq_zero]
    exact (CharP.ringChar_ne_zero_of_finite F).symm
  exact cubicTraceSum_norm_le hF hchar χ hA
    (cubeMultiplicity_character hdiv hχ) hχ₁ hχ₂ (quadraticComplex_ne_one hF) hχφ hχ₂φ

private theorem cube_injective (hdiv : ¬ 3 ∣ Fintype.card F - 1) :
    Function.Injective (fun x : F => x ^ (3 : ℕ)) := by
  intro x y h
  rcases eq_or_ne x 0 with rfl | hx
  · by_contra hn
    exact pow_ne_zero 3 (Ne.symm hn) (by simpa using h.symm)
  rcases eq_or_ne y 0 with rfl | hy
  · by_contra hn
    exact pow_ne_zero 3 hn (by simpa using h)
  let a := Units.mk0 x hx
  let b := Units.mk0 y hy
  have h₃ : (a / b) ^ (3 : ℕ) = 1 := by
    apply Units.ext
    change (x / y) ^ (3 : ℕ) = 1
    rw [div_pow, h, div_self (pow_ne_zero _ hy)]
  have hq : (a / b) ^ (Fintype.card F - 1) = 1 := by
    apply Units.ext
    change ((a / b : Fˣ) : F) ^ (Fintype.card F - 1) = 1
    exact FiniteField.pow_card_sub_one_eq_one _ (a / b).ne_zero
  have hn : Nat.Coprime 3 (Fintype.card F - 1) :=
    Nat.prime_three.coprime_iff_not_dvd.mpr hdiv
  have hg : (a / b) ^ (Nat.gcd 3 (Fintype.card F - 1)) = 1 :=
    pow_gcd_eq_one.mpr ⟨h₃, hq⟩
  rw [show Nat.gcd 3 (Fintype.card F - 1) = 1 from hn, pow_one] at hg
  exact congrArg (fun z : Fˣ => (z : F)) (div_eq_one_iff_eq.mp hg)

private theorem trace_zero_of_no_orderThree (hF : ringChar F ≠ 2)
    (hdiv : ¬ 3 ∣ Fintype.card F - 1) (A : F) : cubicTraceSum A = 0 := by
  let e : F ≃ F := Equiv.ofBijective _ ⟨cube_injective hdiv,
    Finite.surjective_of_injective (cube_injective hdiv)⟩
  change (∑ x : F, quadraticComplex (e x + A)) = 0
  rw [Equiv.sum_comp e (fun z : F => quadraticComplex (z + A))]
  exact quadraticComplex_shift_sum hF A

/-- Hasse's inequality for the native projective point group of this good family. -/
theorem reducedCubic_hasse (hF : ringChar F ≠ 2) {A : F} (hA : A ≠ 0)
    (hΔ : (shortCubic (0 : F) A).Δ ≠ 0) :
    |(Fintype.card F : ℝ) + 1 - (Nat.card (shortCubic (0 : F) A).toProjective.Point : ℝ)| ≤
      2 * Real.sqrt (Fintype.card F : ℝ) := by
  rw [pointTrace_norm_eq hF hΔ]
  by_cases h : 3 ∣ Fintype.card F - 1
  · exact trace_bound_of_orderThree hF h hA
  · rw [trace_zero_of_no_orderThree hF h A, norm_zero]
    exact mul_nonneg zero_le_two (Real.sqrt_nonneg _)

open PrimalitySheafVerification.ManuscriptAudit in
/-- The exact printed good reduction has the claimed Hasse bound at every p ≥ 5. -/
theorem paper5_printed_reduction_hasse (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    {A : ZMod p} (hA : A ≠ 0) :
    |(p : ℝ) + 1 - (Nat.card (paper5TraceCurve p A).toProjective.Point : ℝ)| ≤
      2 * Real.sqrt (p : ℝ) := by
  classical
  have he : shortCubic (0 : ZMod p) A = paper5TraceCurve p A := by
    ext <;> simp [shortCubic, paper5TraceCurve]
  have hF : ringChar (ZMod p) ≠ 2 := by
    rw [ringChar.eq (ZMod p) p]
    omega
  have hΔ : (shortCubic (0 : ZMod p) A).Δ ≠ 0 := by
    rw [he]
    exact paper5_traceCurve_discriminant_ne_zero hp hA
  simpa only [he, ZMod.card p] using reducedCubic_hasse hF hA hΔ

end
end ManuscriptAudit.CubicHasseBound

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CubicHasseBound.reducedCubic_hasse,
      ``ManuscriptAudit.CubicHasseBound.paper5_printed_reduction_hasse] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
