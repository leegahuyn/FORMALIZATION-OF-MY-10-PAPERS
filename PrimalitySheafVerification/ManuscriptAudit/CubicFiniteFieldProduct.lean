import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassFiniteFieldFixedCount

/-! Product of the native cubic equation at every element of a split finite field. -/

namespace ManuscriptAudit.CubicFiniteFieldProduct

open Polynomial

noncomputable section

variable (K L : Type*) [Field K] [Fintype K] [DecidableEq K]
  [Field L] [Algebra K L]

/-- The exact product over every base-field linear factor, evaluated in an extension. -/
theorem product_sub_scalar (hchar : ringChar K ≠ 2) (y : L) :
    (∏ x : K, algebraMap K L x - y) = y - y ^ Fintype.card K := by
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  let P : K[X] := X ^ Fintype.card K - X
  have hSplit : P.Splits := by
    rw [splits_iff_card_roots]
    change (X ^ Fintype.card K - X : K[X]).roots.card =
      (X ^ Fintype.card K - X : K[X]).natDegree
    rw [FiniteField.roots_X_pow_card_sub_X, ← Finset.card_def, Finset.card_univ,
      FiniteField.X_pow_card_sub_X_natDegree_eq K hq]
  have hMonic : P.Monic := by
    apply monic_X_pow_sub
    rw [degree_X]
    exact_mod_cast hq
  have hfactor : P = ∏ x : K, (X - C x) := by
    have h := hSplit.eq_prod_roots_of_monic hMonic
    change P = ((X ^ Fintype.card K - X : K[X]).roots.map (fun x => X - C x)).prod at h
    rw [FiniteField.roots_X_pow_card_sub_X] at h
    exact h
  have heval : (∏ x : K, (y - algebraMap K L x)) = y ^ Fintype.card K - y := by
    have h := congrArg (aeval y : K[X] →ₐ[K] L) hfactor.symm
    simpa only [P, map_prod, map_sub, map_pow, aeval_X, aeval_C] using h
  have hodd : Odd (Fintype.card K) := Nat.odd_iff.mpr (FiniteField.odd_card_of_char_ne_two hchar)
  calc
    _ = ∏ x : K, -(y - algebraMap K L x) := by simp only [neg_sub]
    _ = (-1 : L) * (y ^ Fintype.card K - y) := by
      rw [Finset.prod_neg, Finset.card_univ, hodd.neg_one_pow, heval]
    _ = _ := by ring

theorem cube_root_relation {F : Type*} [Field F] {z : F} (hz : IsPrimitiveRoot z 3) :
    z ^ 2 + z + 1 = 0 := by
  have h : (z - 1) * (z ^ 2 + z + 1) = 0 := by
    calc
      _ = z ^ 3 - 1 := by ring
      _ = 0 := sub_eq_zero.mpr hz.pow_eq_one
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr (hz.ne_one (by decide)))

private theorem factor_three {F : Type*} [Field F] {t z A : F}
    (hz : IsPrimitiveRoot z 3) (ht : t ^ 3 = -A) (x : F) :
    x ^ 3 + A = (x - t) * (x - z * t) * (x - z ^ 2 * t) := by
  have hs := cube_root_relation hz
  have h := hz.pow_eq_one
  calc
    _ = x ^ 3 - t ^ 3 := by rw [ht, sub_neg_eq_add]
    _ = x ^ 3 - (z ^ 2 + z + 1) * x ^ 2 * t +
        (z ^ 3 + z ^ 2 + z) * x * t ^ 2 - z ^ 3 * t ^ 3 := by
      rw [hs, h, show (1 : F) + z ^ 2 + z = 0 by linear_combination hs]
      ring
    _ = _ := by ring

/-- The product of the centered cubic across the finite field is determined by the
scalar that cycles a chosen cubic root under Frobenius. -/
theorem product_cubic_of_frobenius_ratio (hchar : ringChar K ≠ 2)
    {A z c : K} (hz : IsPrimitiveRoot z 3) {t : L}
    (ht : t ^ 3 = -algebraMap K L A)
    (hCycle : t ^ Fintype.card K = algebraMap K L c * t) :
    (∏ x : K, (x ^ 3 + A)) = A * (c - 1) ^ 3 := by
  let u := algebraMap K L z
  let v := algebraMap K L c
  have hu := hz.map_of_injective (algebraMap K L).injective
  have huFix : u ^ Fintype.card K = u := by
    dsimp only [u]
    rw [← map_pow, FiniteField.pow_card]
  have hRatio : t ^ Fintype.card K = v * t := hCycle
  apply (algebraMap K L).injective
  simp only [map_prod, map_add, map_pow, map_mul, map_sub, map_one]
  calc
    _ = ∏ x : K, ((algebraMap K L x - t) * (algebraMap K L x - u * t) *
        (algebraMap K L x - u ^ 2 * t)) := by
      apply Finset.prod_congr rfl
      intro x _
      exact factor_three hu ht (algebraMap K L x)
    _ = (t - t ^ Fintype.card K) * (u * t - (u * t) ^ Fintype.card K) *
        (u ^ 2 * t - (u ^ 2 * t) ^ Fintype.card K) := by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, product_sub_scalar K L hchar,
        product_sub_scalar K L hchar, product_sub_scalar K L hchar]
    _ = (1 - v) ^ 3 * u ^ 3 * t ^ 3 := by
      rw [mul_pow, mul_pow, pow_right_comm u 2 (Fintype.card K), huFix, hRatio]
      ring
    _ = _ := by
      rw [hu.pow_eq_one, ht]
      dsimp only [v]
      ring

end
end ManuscriptAudit.CubicFiniteFieldProduct

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicFiniteFieldProduct.product_sub_scalar,
      ``ManuscriptAudit.CubicFiniteFieldProduct.product_cubic_of_frobenius_ratio] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
