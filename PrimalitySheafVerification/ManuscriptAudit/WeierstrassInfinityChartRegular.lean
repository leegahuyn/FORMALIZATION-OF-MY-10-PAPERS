import Lean.Util.CollectAxioms
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Bivariate
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassInfinityChartAlgebra

/-! The actual local parameter at the rational origin of the infinity chart is regular. -/

namespace ManuscriptAudit.WeierstrassInfinityChartRegular

open Polynomial WeierstrassInfinityChartAlgebra
open scoped Polynomial.Bivariate nonZeroDivisors

universe u

noncomputable section

variable {K : Type u} [Field K] (W : WeierstrassCurve.Affine K)

private theorem mk_mem_nonZeroDivisors {p a : K[X][Y]} (ha : Prime a) (hap : ¬ a ∣ p) :
    AdjoinRoot.mk p a ∈ (AdjoinRoot p)⁰ := by
  apply mem_nonZeroDivisors_iff_left.mpr
  intro t ht
  obtain ⟨s, rfl⟩ := AdjoinRoot.mk_surjective (g := p) t
  rw [← map_mul, AdjoinRoot.mk_eq_zero] at ht
  obtain ⟨b, hb⟩ := ht
  have hab : a ∣ p * b := by rw [← hb]; exact dvd_mul_right a s
  obtain ⟨c, hc⟩ := (ha.dvd_mul.mp hab).resolve_left hap
  have he : a * s = a * (p * c) := by
    rw [hb, hc]
    ac_rfl
  exact AdjoinRoot.mk_eq_zero.mpr ⟨c, mul_left_cancel₀ ha.ne_zero he⟩

private theorem const_x_prime : Prime (C (X : K[X]) : K[X][Y]) := by
  let e := Polynomial.Bivariate.swap (R := K)
  have hy : Prime (Y : K[X][Y]) := Polynomial.prime_X
  have hX : e (C (X : K[X])) = Y := Polynomial.Bivariate.swap_X
  have hY : e.symm (Y : K[X][Y]) = C X := by
    change (Polynomial.Bivariate.swap (R := K)).symm Y = C X
    rw [Polynomial.Bivariate.swap_symm, Polynomial.Bivariate.swap_Y]
  refine ⟨C_ne_zero.mpr X_ne_zero, ?_, ?_⟩
  · intro h
    have he := h.map e.toRingHom
    change IsUnit (e (C (X : K[X]))) at he
    rw [hX] at he
    exact hy.2.1 he
  · intro a b h
    have he := map_dvd e.toRingHom h
    change e (C (X : K[X])) ∣ e (a * b) at he
    rw [hX, map_mul] at he
    rcases hy.dvd_mul.mp he with h' | h'
    · left
      have hd := map_dvd e.symm.toRingHom h'
      change e.symm Y ∣ e.symm (e a) at hd
      rwa [hY, e.symm_apply_apply] at hd
    · right
      have hd := map_dvd e.symm.toRingHom h'
      change e.symm Y ∣ e.symm (e b) at hd
      rwa [hY, e.symm_apply_apply] at hd

private theorem const_x_not_dvd : ¬ (C (X : K[X]) : K[X][Y]) ∣ equation W := by
  let f : K[X][Y] →+* K[X] := Polynomial.mapRingHom (Polynomial.evalRingHom (0 : K))
  have hf : f (C (X : K[X])) = 0 := by simp [f]
  have hp : f (equation W) = X * (1 + C W.a₃ * X - C W.a₆ * X ^ 2) := by
    simp [f, equation, bracketPolynomial]
  intro h
  have hmap : f (C (X : K[X])) ∣ f (equation W) := map_dvd f h
  rw [hf, zero_dvd_iff, hp] at hmap
  have hc := congrArg (fun p : K[X] => p.coeff (0 + 1)) hmap
  change (X * (1 + C W.a₃ * X - C W.a₆ * X ^ 2)).coeff (0 + 1) = (0 : K[X]).coeff (0 + 1) at hc
  rw [Polynomial.coeff_X_mul, Polynomial.coeff_zero_eq_eval_zero] at hc
  exact (one_ne_zero : (1 : K) ≠ 0) (by simpa using hc)

private theorem y_not_dvd : ¬ (Y : K[X][Y]) ∣ equation W := by
  intro h
  have hc := Polynomial.X_dvd_iff.mp h
  have he : (C (X : K[X]) : K[X][Y]) ^ 3 = C ((X : K[X]) ^ 3) :=
    (map_pow Polynomial.C (X : K[X]) 3).symm
  rw [equation, he, Polynomial.coeff_sub, Polynomial.coeff_X_mul_zero,
    Polynomial.coeff_C_zero, zero_sub] at hc
  exact (pow_ne_zero 3 (X_ne_zero : (X : K[X]) ≠ 0)) (neg_eq_zero.mp hc)

/-- X/Y is a non-zero-divisor in the literal infinity chart ring. -/
theorem x_regular : x W ∈ (Ring W)⁰ :=
  mk_mem_nonZeroDivisors const_x_prime (const_x_not_dvd W)

/-- Z/Y is a non-zero-divisor in the literal infinity chart ring. -/
theorem z_regular : z W ∈ (Ring W)⁰ :=
  mk_mem_nonZeroDivisors Polynomial.prime_X (y_not_dvd W)

/-- The single ideal generator remains a non-zero-divisor near the rational origin. -/
theorem localX_regular : localX W ∈ (Neighborhood W)⁰ :=
  IsLocalization.map_nonZeroDivisors_le
    (M := Submonoid.powers (bracket W)) (S := Neighborhood W) ⟨x W, x_regular W, rfl⟩

end

end ManuscriptAudit.WeierstrassInfinityChartRegular

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassInfinityChartRegular.x_regular,
      ``ManuscriptAudit.WeierstrassInfinityChartRegular.z_regular,
      ``ManuscriptAudit.WeierstrassInfinityChartRegular.localX_regular] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
