import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicHasseBound

/-! The two actual Jacobi roots of the local point-count polynomial. -/

namespace ManuscriptAudit.CubicJacobiRoots

open FiniteFieldPointCount CubicJacobiBound CubicCharacterMultiplicity JacobiComplexNorm

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The Jacobi term with the point-trace sign and its parameter scaling. -/
def jacobiRoot (χ : MulChar F ℂ) (A : F) : ℂ :=
  χ (-A) * quadraticComplex A * (-jacobiSum χ quadraticComplex)

theorem projective_count_trace_complex (hF : ringChar F ≠ 2) {A : F}
    (hΔ : (shortCubic (0 : F) A).Δ ≠ 0) :
    (Fintype.card F : ℂ) + 1 -
      (Nat.card (shortCubic (0 : F) A).toProjective.Point : ℂ) = -cubicTraceSum A := by
  have hc := shortCubic_projective_count_int hF hΔ
  simp only [zero_mul, sub_zero] at hc
  have he := congrArg (fun x : ℤ => (x : ℂ)) hc
  push_cast at he
  change (Fintype.card F : ℂ) + 1 -
    (Nat.card (shortCubic (0 : F) A).toProjective.Point : ℂ) =
      -(∑ x : F, (quadraticChar F (x ^ 3 + A) : ℂ))
  rw [he]
  ring

theorem cubicTraceSum_eq_neg_jacobiRoots (hF : ringChar F ≠ 2)
    {χ : MulChar F ℂ} (hχ : orderOf χ = 3) {A : F} (hA : A ≠ 0) :
    -cubicTraceSum A = jacobiRoot χ A + jacobiRoot (χ ^ 2) A := by
  have hdiv := MulChar.orderOf_dvd_card_sub_one F χ
  rw [hχ] at hdiv
  rw [cubicTraceSum_eq hF χ hA (cubeMultiplicity_character hdiv hχ)]
  unfold jacobiRoot
  ring

private theorem cube_inv_eq_sq {χ : MulChar F ℂ} (hχ : orderOf χ = 3) :
    χ⁻¹ = χ ^ 2 := by
  have h : χ ^ (3 : ℕ) = 1 := by simpa only [hχ] using pow_orderOf_eq_one χ
  have he : χ * χ ^ (2 : ℕ) = 1 := by rw [← pow_succ', h]
  calc
    χ⁻¹ = χ⁻¹ * 1 := (mul_one _).symm
    _ = χ⁻¹ * (χ * χ ^ (2 : ℕ)) := by rw [he]
    _ = χ ^ 2 := by rw [← mul_assoc, inv_mul_cancel, one_mul]

private theorem quadratic_inv :
    (quadraticComplex : MulChar F ℂ)⁻¹ = quadraticComplex := by
  let θ : MulChar F ℂ := quadraticComplex
  have he : θ * θ = 1 := by
    rw [← pow_two]
    exact CubicHasseBound.quadraticComplex_sq
  change θ⁻¹ = θ
  calc
    θ⁻¹ = θ⁻¹ * 1 := (mul_one _).symm
    _ = θ⁻¹ * (θ * θ) := by rw [he]
    _ = θ := by rw [← mul_assoc, inv_mul_cancel, one_mul]

theorem jacobiRoots_conjugate {χ : MulChar F ℂ} (hχ : orderOf χ = 3) (A : F) :
    jacobiRoot (χ ^ 2) A = (starRingEnd ℂ) (jacobiRoot χ A) := by
  simp only [jacobiRoot, map_mul, map_neg, ← invCharacter_eq_conj, ← jacobiSum_inv_eq_conj,
    cube_inv_eq_sq hχ, quadratic_inv]

theorem jacobiRoot_norm (hF : ringChar F ≠ 2) {χ : MulChar F ℂ}
    (hχ : orderOf χ = 3) {A : F} (hA : A ≠ 0) :
    ‖jacobiRoot χ A‖ = Real.sqrt (Fintype.card F : ℝ) := by
  have hχ₁ : χ ≠ 1 := by
    simpa only [pow_one] using CubicHasseBound.ne_one_of_orderThree_pow hχ
      (by decide : ¬ 3 ∣ (1 : ℕ))
  have hχ₂ := CubicHasseBound.ne_one_of_orderThree_pow hχ (by decide : ¬ 3 ∣ (2 : ℕ))
  have hχφ : χ * quadraticComplex ≠ 1 := by
    intro h
    exact hχ₂ (by rw [CubicHasseBound.mul_quadratic_eq_one h, CubicHasseBound.quadraticComplex_sq])
  have hchar : ringChar ℂ ≠ ringChar F := by
    rw [ringChar.eq_zero]
    exact (CharP.ringChar_ne_zero_of_finite F).symm
  rw [jacobiRoot, norm_mul, norm_mul, norm_neg, character_norm_one χ (neg_ne_zero.mpr hA),
    character_norm_one quadraticComplex hA, one_mul, one_mul,
    norm_jacobiSum hchar hχ₁ (CubicHasseBound.quadraticComplex_ne_one hF) hχφ]

theorem jacobiRoots_product (hF : ringChar F ≠ 2) {χ : MulChar F ℂ}
    (hχ : orderOf χ = 3) {A : F} (hA : A ≠ 0) :
    jacobiRoot χ A * jacobiRoot (χ ^ 2) A = (Fintype.card F : ℂ) := by
  rw [jacobiRoots_conjugate hχ A, Complex.mul_conj', jacobiRoot_norm hF hχ hA,
    ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]

end
end ManuscriptAudit.CubicJacobiRoots

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicJacobiRoots.projective_count_trace_complex,
      ``ManuscriptAudit.CubicJacobiRoots.cubicTraceSum_eq_neg_jacobiRoots,
      ``ManuscriptAudit.CubicJacobiRoots.jacobiRoots_conjugate,
      ``ManuscriptAudit.CubicJacobiRoots.jacobiRoot_norm,
      ``ManuscriptAudit.CubicJacobiRoots.jacobiRoots_product] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
