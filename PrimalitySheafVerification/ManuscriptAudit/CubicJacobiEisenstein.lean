import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ComplexEisensteinCoordinates
import PrimalitySheafVerification.ManuscriptAudit.CubicJacobiRoots

/-! Exact integral Eisenstein coordinates for the arithmetic Jacobi roots of split centered cubics. -/

namespace ManuscriptAudit.CubicJacobiEisenstein

open FiniteFieldPointCount CubicJacobiBound CubicCharacterMultiplicity CubicJacobiRoots
open ComplexEisensteinCoordinates

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private theorem cubicCharacter_mem {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 3)
    {χ : MulChar F ℂ} (hχ : orderOf χ = 3) (x : F) :
    χ x ∈ eisensteinSubring ζ hζ := by
  classical
  by_cases hx : x = 0
  · rw [hx, χ.map_zero]
    exact (eisensteinSubring ζ hζ).zero_mem
  · have h₃ : χ ^ 3 = 1 := by simpa only [hχ] using pow_orderOf_eq_one χ
    have hpow : χ x ^ 3 = 1 := by
      rw [← MulChar.pow_apply' χ (by decide : (3 : ℕ) ≠ 0) x, h₃,
        MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)]
    obtain ⟨j, _, hj⟩ := hζ.eq_pow_of_pow_eq_one hpow
    rw [← hj]
    exact (eisensteinSubring ζ hζ).pow_mem (root_mem hζ) _

private theorem quadraticCharacter_mem {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 3) (x : F) :
    quadraticComplex x ∈ eisensteinSubring ζ hζ := by
  change (quadraticChar F x : ℂ) ∈ eisensteinSubring ζ hζ
  exact intCast_mem _ _

/-- The actual complex Jacobi root of the point-count polynomial has integral coordinates. -/
theorem jacobiRoot_coordinates {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 3)
    {χ : MulChar F ℂ} (hχ : orderOf χ = 3) (A : F) :
    ∃ a b : ℤ, jacobiRoot χ A = (a : ℂ) + (b : ℂ) * ζ := by
  let S := eisensteinSubring ζ hζ
  change jacobiRoot χ A ∈ S
  have hJ : jacobiSum χ quadraticComplex ∈ S := by
    unfold jacobiSum
    exact S.sum_mem (fun x _ =>
      S.mul_mem (cubicCharacter_mem hζ hχ x) (quadraticCharacter_mem hζ (1 - x)))
  unfold jacobiRoot
  exact S.mul_mem (S.mul_mem (cubicCharacter_mem hζ hχ (-A)) (quadraticCharacter_mem hζ A))
    (S.neg_mem hJ)

/-- The signed projective point count and field size are the exact trace and norm of an integral pair. -/
theorem exists_integral_trace_norm (hF : ringChar F ≠ 2)
    (hsplit : 3 ∣ Fintype.card F - 1) {A : F} (hA : A ≠ 0)
    (hΔ : (shortCubic (0 : F) A).Δ ≠ 0) :
    ∃ a b : ℤ,
      (Fintype.card F : ℤ) + 1 - (Nat.card (shortCubic (0 : F) A).toProjective.Point : ℤ) =
        2 * a - b ∧
      (Fintype.card F : ℤ) = a ^ 2 - a * b + b ^ 2 := by
  let ζ : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 3)
  have hζ : IsPrimitiveRoot ζ 3 := Complex.isPrimitiveRoot_exp 3 (by decide)
  obtain ⟨χ, hχ⟩ := exists_orderThree_character (F := F) hsplit
  obtain ⟨a, b, he⟩ := jacobiRoot_coordinates hζ hχ A
  refine ⟨a, b, ?_, ?_⟩
  · apply (Int.cast_injective (α := ℂ))
    push_cast
    rw [projective_count_trace_complex hF hΔ, cubicTraceSum_eq_neg_jacobiRoots hF hχ hA,
      jacobiRoots_conjugate hχ A, he]
    simpa only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat] using trace_coordinates hζ a b
  · apply (Int.cast_injective (α := ℂ))
    push_cast
    have hprod := jacobiRoots_product hF hχ hA
    rw [jacobiRoots_conjugate hχ A, he] at hprod
    exact hprod.symm.trans (by
      simpa only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_pow] using
        norm_coordinates hζ a b)

end
end ManuscriptAudit.CubicJacobiEisenstein

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicJacobiEisenstein.jacobiRoot_coordinates,
      ``ManuscriptAudit.CubicJacobiEisenstein.exists_integral_trace_norm] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
