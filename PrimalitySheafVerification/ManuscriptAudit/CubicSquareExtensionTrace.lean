import Lean.Util.CollectAxioms
import Mathlib.Tactic.LinearCombination
import PrimalitySheafVerification.ManuscriptAudit.CubicJacobiRoots
import PrimalitySheafVerification.ManuscriptAudit.CubicPointCountModuloThree

namespace ManuscriptAudit.CubicSquareExtensionTrace

open CubicJacobiRoots CubicJacobiBound CubicHasseBound CubicCharacterMultiplicity
open CubicPointCountModuloThree FiniteFieldPointCount
open scoped BigOperators

noncomputable section

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  [CharP F p]

theorem jacobiSum_pow_frobenius (χ φ : MulChar F ℂ) :
    jacobiSum χ φ = jacobiSum (χ ^ p) (φ ^ p) := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  let f := frobenius F p
  let e : F ≃ F := Equiv.ofBijective f ⟨f.injective, Finite.surjective_of_injective f.injective⟩
  calc
    _ = ∑ x : F, χ (e x) * φ (1 - e x) :=
      (Equiv.sum_comp e (fun x : F => χ x * φ (1 - x))).symm
    _ = _ := by
      unfold jacobiSum
      apply Finset.sum_congr rfl
      intro x _
      change χ (f x) * φ (1 - f x) = (χ ^ p) x * (φ ^ p) (1 - x)
      have h : 1 - f x = f (1 - x) := by rw [map_sub, map_one]
      rw [h]
      change χ (x ^ p) * φ ((1 - x) ^ p) = (χ ^ p) x * (φ ^ p) (1 - x)
      simp only [map_pow, MulChar.pow_apply' χ hp, MulChar.pow_apply' φ hp]

private theorem quadraticComplex_order_two (hF : ringChar F ≠ 2) :
    orderOf (quadraticComplex : MulChar F ℂ) = 2 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (orderOf_eq_prime_iff (p := 2)).mpr ⟨quadraticComplex_sq, quadraticComplex_ne_one hF⟩

theorem jacobiSum_eq_cubicSquare (hp3 : p % 3 = 2) (hp2 : p % 2 = 1)
    (hF : ringChar F ≠ 2) {χ : MulChar F ℂ} (hχ : orderOf χ = 3) :
    jacobiSum χ quadraticComplex = jacobiSum (χ ^ 2) quadraticComplex := by
  have h := jacobiSum_pow_frobenius (p := p) χ quadraticComplex
  rw [← pow_mod_orderOf χ p, hχ, hp3,
    ← pow_mod_orderOf (quadraticComplex : MulChar F ℂ) p,
    quadraticComplex_order_two hF, hp2, pow_one] at h
  exact h

private theorem cubicChar_neg_one {χ : MulChar F ℂ} (hχ : orderOf χ = 3) :
    χ (-1) = 1 := by
  have h₂ : χ (-1) ^ (2 : ℕ) = 1 := by rw [← map_pow, neg_one_sq, map_one]
  have h₃ : χ (-1) ^ (3 : ℕ) = 1 := by
    have h : χ ^ (3 : ℕ) = 1 := by simpa only [hχ] using pow_orderOf_eq_one χ
    rw [← MulChar.pow_apply' χ (by decide : (3 : ℕ) ≠ 0), h,
      MulChar.one_apply ((neg_ne_zero.mpr (one_ne_zero : (1 : F) ≠ 0)).isUnit)]
  simpa only [pow_succ _ 2, h₂, one_mul] using h₃

theorem jacobiRoots_eq_at_one (hp3 : p % 3 = 2) (hp2 : p % 2 = 1)
    (hF : ringChar F ≠ 2) {χ : MulChar F ℂ} (hχ : orderOf χ = 3) :
    jacobiRoot χ (1 : F) = jacobiRoot (χ ^ 2) (1 : F) := by
  simp only [jacobiRoot, MulChar.pow_apply' χ (by decide : (2 : ℕ) ≠ 0), cubicChar_neg_one hχ,
    map_one, one_mul, one_pow, jacobiSum_eq_cubicSquare hp3 hp2 hF hχ]

theorem square_extension_jacobiRoot (hp3 : p % 3 = 2) (hp2 : p % 2 = 1)
    (hF : ringChar F ≠ 2) (hq : Fintype.card F = p ^ 2)
    (hΔ : (shortCubic (0 : F) 1).Δ ≠ 0) {χ : MulChar F ℂ} (hχ : orderOf χ = 3) :
    jacobiRoot χ (1 : F) = -(p : ℂ) := by
  have heq := jacobiRoots_eq_at_one hp3 hp2 hF hχ
  have hm := jacobiRoots_product hF hχ (one_ne_zero : (1 : F) ≠ 0)
  rw [← heq, hq, Nat.cast_pow] at hm
  have hsq : (jacobiRoot χ (1 : F)) ^ 2 = (p : ℂ) ^ 2 := by
    simpa only [pow_two] using hm
  have hz : (jacobiRoot χ (1 : F) - (p : ℂ)) *
      (jacobiRoot χ (1 : F) + (p : ℂ)) = 0 := by
    linear_combination hsq
  rcases mul_eq_zero.mp hz with hpos | hneg
  · exfalso
    have hroot := sub_eq_zero.mp hpos
    have hpcast : (p : ZMod 3) = 2 := by
      exact (ZMod.natCast_eq_natCast_iff p 2 3).mpr (by simpa [Nat.ModEq] using hp3)
    have hqcast : (Fintype.card F : ZMod 3) = 1 := by
      rw [hq, Nat.cast_pow, hpcast] <;> decide
    have hdiv := MulChar.orderOf_dvd_card_sub_one F χ
    rw [hχ] at hdiv
    have hcount := count_cast_zmod_three_zero hF hqcast hdiv hΔ
    have htrace := (projective_count_trace_complex hF hΔ).trans
      (cubicTraceSum_eq_neg_jacobiRoots hF hχ (one_ne_zero : (1 : F) ≠ 0))
    rw [← heq, hroot] at htrace
    have hi : (Fintype.card F : ℤ) + 1 -
        (Nat.card (shortCubic (0 : F) 1).toProjective.Point : ℤ) = (p : ℤ) + (p : ℤ) := by
      exact_mod_cast htrace
    have hmod := congrArg (fun x : ℤ => (x : ZMod 3)) hi
    push_cast at hmod
    rw [hqcast, hpcast, hcount] at hmod
    exact (by decide : (1 : ZMod 3) + 1 - 0 ≠ 2 + 2) hmod
  · calc
      jacobiRoot χ (1 : F) = (jacobiRoot χ (1 : F) + (p : ℂ)) - (p : ℂ) := by ring
      _ = -(p : ℂ) := by rw [hneg, zero_sub]

theorem square_extension_projective_count (hp3 : p % 3 = 2) (hp2 : p % 2 = 1)
    (hF : ringChar F ≠ 2) (hq : Fintype.card F = p ^ 2)
    (hΔ : (shortCubic (0 : F) 1).Δ ≠ 0) (hdiv : 3 ∣ Fintype.card F - 1) :
    Nat.card (shortCubic (0 : F) 1).toProjective.Point = p ^ 2 + 1 + 2 * p := by
  obtain ⟨χ, hχ⟩ := exists_orderThree_character (F := F) hdiv
  have heq := jacobiRoots_eq_at_one hp3 hp2 hF hχ
  have htrace := (projective_count_trace_complex hF hΔ).trans
    (cubicTraceSum_eq_neg_jacobiRoots hF hχ (one_ne_zero : (1 : F) ≠ 0))
  rw [← heq, square_extension_jacobiRoot hp3 hp2 hF hq hΔ hχ, hq, Nat.cast_pow] at htrace
  have hi : (p : ℤ) ^ 2 + 1 -
      (Nat.card (shortCubic (0 : F) 1).toProjective.Point : ℤ) =
        -(p : ℤ) + -(p : ℤ) := by
    exact_mod_cast htrace
  have hcount : (Nat.card (shortCubic (0 : F) 1).toProjective.Point : ℤ) =
      (p : ℤ) ^ 2 + 1 + 2 * (p : ℤ) := by omega
  exact_mod_cast hcount

end
end ManuscriptAudit.CubicSquareExtensionTrace

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicSquareExtensionTrace.jacobiSum_pow_frobenius,
      ``ManuscriptAudit.CubicSquareExtensionTrace.jacobiSum_eq_cubicSquare,
      ``ManuscriptAudit.CubicSquareExtensionTrace.jacobiRoots_eq_at_one,
      ``ManuscriptAudit.CubicSquareExtensionTrace.square_extension_jacobiRoot,
      ``ManuscriptAudit.CubicSquareExtensionTrace.square_extension_projective_count] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
