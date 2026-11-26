import Lean.Util.CollectAxioms
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic.Ring

/-! The Möbius coordinate u=(t−1)/(t+1) identifies the normalized
punctured affine nodal chart with the open u≠1 of the multiplicative group. -/

namespace ManuscriptAudit.NodalSmoothMobius

open Polynomial

noncomputable section

universe u

variable (K : Type u) [Field K]

def tDenominator : Polynomial K := Polynomial.X ^ 2 - 1
def uDenominator : Polynomial K := Polynomial.X * (Polynomial.X - 1)

abbrev tRing := Localization.Away (tDenominator K)
abbrev uRing := Localization.Away (uDenominator K)

def t : tRing K := algebraMap (Polynomial K) (tRing K) Polynomial.X
def u : uRing K := algebraMap (Polynomial K) (uRing K) Polynomial.X

private theorem t_factors_unit : IsUnit ((t K - 1) * (t K + 1)) := by
  let f := algebraMap (Polynomial K) (tRing K)
  have h : f (tDenominator K) = (t K - 1) * (t K + 1) := by
    calc
      _ = f ((Polynomial.X : Polynomial K) ^ 2) - f 1 := f.map_sub _ _
      _ = t K ^ 2 - 1 := congrArg₂ (· - ·) (map_pow f Polynomial.X 2) f.map_one
      _ = _ := by ring
  exact h ▸ IsLocalization.Away.algebraMap_isUnit (S := tRing K) (tDenominator K)

private theorem t_minus_one_unit : IsUnit (t K - 1) := (IsUnit.mul_iff.mp (t_factors_unit K)).1
private theorem t_plus_one_unit : IsUnit (t K + 1) := (IsUnit.mul_iff.mp (t_factors_unit K)).2

private theorem u_factors_unit : IsUnit (u K * (u K - 1)) := by
  let f := algebraMap (Polynomial K) (uRing K)
  have h : f (uDenominator K) = u K * (u K - 1) := by
    calc
      _ = f Polynomial.X * f (Polynomial.X - 1) := f.map_mul _ _
      _ = _ := congrArg (f Polynomial.X * ·)
        ((f.map_sub Polynomial.X 1).trans (congrArg (f Polynomial.X - ·) f.map_one))
  exact h ▸ IsLocalization.Away.algebraMap_isUnit (S := uRing K) (uDenominator K)

private theorem u_unit : IsUnit (u K) := (IsUnit.mul_iff.mp (u_factors_unit K)).1
private theorem u_minus_one_unit : IsUnit (u K - 1) := (IsUnit.mul_iff.mp (u_factors_unit K)).2

private def tPlusOneInv : tRing K := (↑((t_plus_one_unit K).unit⁻¹) : tRing K)
private def uMinusOneInv : uRing K := (↑((u_minus_one_unit K).unit⁻¹) : uRing K)

private theorem tPlusOne_mul_inv : (t K + 1) * tPlusOneInv K = 1 :=
  (t_plus_one_unit K).mul_val_inv
private theorem uMinusOne_mul_inv : (u K - 1) * uMinusOneInv K = 1 :=
  (u_minus_one_unit K).mul_val_inv

/-- The actual coordinate (t−1)/(t+1). -/
def uAtT : tRing K := (t K - 1) * tPlusOneInv K

/-- The actual inverse coordinate (1+u)/(1−u). -/
def tAtU : uRing K := -(u K + 1) * uMinusOneInv K

theorem uAtT_times_tplus : uAtT K * (t K + 1) = t K - 1 := by
  unfold uAtT
  rw [mul_assoc, mul_comm (tPlusOneInv K), tPlusOne_mul_inv, mul_one]

theorem tAtU_times_uminus : tAtU K * (u K - 1) = -(u K + 1) := by
  unfold tAtU
  rw [mul_assoc, mul_comm (uMinusOneInv K), uMinusOne_mul_inv, mul_one]

private theorem two_unit {S : Type u} [CommRing S] [Algebra K S] (h2 : (2 : K) ≠ 0) :
    IsUnit (2 : S) := by
  let f := algebraMap K S
  have hf : f (2 : K) = (2 : S) := by
    have h : f ((1 : K) + 1) = (1 : S) + 1 :=
      (f.map_add 1 1).trans (congrArg₂ (· + ·) f.map_one f.map_one)
    simpa only [one_add_one_eq_two] using h
  rw [← hf]
  exact (isUnit_iff_ne_zero.mpr h2).map f

private theorem uAtT_unit : IsUnit (uAtT K) :=
  (t_minus_one_unit K).mul ((t_plus_one_unit K).unit⁻¹).isUnit

private theorem uAtT_minus_one_unit (h2 : (2 : K) ≠ 0) : IsUnit (uAtT K - 1) := by
  have h : uAtT K - 1 = -(2 : tRing K) * tPlusOneInv K := by
    calc
      _ = (t K - 1) * tPlusOneInv K - (t K + 1) * tPlusOneInv K := by rw [tPlusOne_mul_inv] <;> rfl
      _ = _ := by ring
  rw [h]
  exact (two_unit K h2).neg.mul ((t_plus_one_unit K).unit⁻¹).isUnit

private theorem tAtU_minus_one_unit (h2 : (2 : K) ≠ 0) : IsUnit (tAtU K - 1) := by
  have h : tAtU K - 1 = -(2 : uRing K) * u K * uMinusOneInv K := by
    calc
      _ = -(u K + 1) * uMinusOneInv K - (u K - 1) * uMinusOneInv K := by rw [uMinusOne_mul_inv] <;> rfl
      _ = _ := by ring
  rw [h]
  exact ((two_unit K h2).neg.mul (u_unit K)).mul ((u_minus_one_unit K).unit⁻¹).isUnit

private theorem tAtU_plus_one_unit (h2 : (2 : K) ≠ 0) : IsUnit (tAtU K + 1) := by
  have h : tAtU K + 1 = -(2 : uRing K) * uMinusOneInv K := by
    calc
      _ = -(u K + 1) * uMinusOneInv K + (u K - 1) * uMinusOneInv K := by rw [uMinusOne_mul_inv] <;> rfl
      _ = _ := by ring
  rw [h]
  exact (two_unit K h2).neg.mul ((u_minus_one_unit K).unit⁻¹).isUnit

private theorem uDenominator_at_T_unit (h2 : (2 : K) ≠ 0) :
    IsUnit (Polynomial.aeval (uAtT K) (uDenominator K)) := by
  unfold uDenominator
  rw [map_mul, map_sub, map_one, Polynomial.aeval_X]
  exact (uAtT_unit K).mul (uAtT_minus_one_unit K h2)

private theorem tDenominator_at_U_unit (h2 : (2 : K) ≠ 0) :
    IsUnit (Polynomial.aeval (tAtU K) (tDenominator K)) := by
  unfold tDenominator
  rw [map_sub, map_pow, map_one, Polynomial.aeval_X]
  rw [show tAtU K ^ 2 - 1 = (tAtU K - 1) * (tAtU K + 1) by ring]
  exact (tAtU_minus_one_unit K h2).mul (tAtU_plus_one_unit K h2)

def uToT (h2 : (2 : K) ≠ 0) : uRing K →ₐ[K] tRing K :=
  IsLocalization.Away.liftAlgHom (uDenominator K) (f := Polynomial.aeval (uAtT K))
    (uDenominator_at_T_unit K h2)

def tToU (h2 : (2 : K) ≠ 0) : tRing K →ₐ[K] uRing K :=
  IsLocalization.Away.liftAlgHom (tDenominator K) (f := Polynomial.aeval (tAtU K))
    (tDenominator_at_U_unit K h2)

theorem uToT_u (h2 : (2 : K) ≠ 0) : uToT K h2 (u K) = uAtT K := by
  unfold uToT u
  rw [IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  exact Polynomial.aeval_X (R := K) _

theorem tToU_t (h2 : (2 : K) ≠ 0) : tToU K h2 (t K) = tAtU K := by
  unfold tToU t
  rw [IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  exact Polynomial.aeval_X (R := K) _

theorem uToT_tAtU (h2 : (2 : K) ≠ 0) : uToT K h2 (tAtU K) = t K := by
  have h := congrArg (uToT K h2) (tAtU_times_uminus K)
  simp only [map_mul, map_sub, map_neg, map_add, map_one, uToT_u] at h
  apply (uAtT_minus_one_unit K h2).mul_left_inj.mp
  calc
    _ = -(uAtT K + 1) := h
    _ = uAtT K * (t K + 1) - (t K - 1) - (uAtT K + 1) := by
      rw [uAtT_times_tplus, sub_self, zero_sub]
    _ = _ := by ring

theorem tToU_uAtT (h2 : (2 : K) ≠ 0) : tToU K h2 (uAtT K) = u K := by
  have h := congrArg (tToU K h2) (uAtT_times_tplus K)
  simp only [map_mul, map_sub, map_add, map_one, tToU_t] at h
  apply (tAtU_plus_one_unit K h2).mul_left_inj.mp
  calc
    _ = tAtU K - 1 := h
    _ = tAtU K * (u K - 1) + (u K + 1) + (tAtU K - 1) := by
      rw [tAtU_times_uminus, neg_add_cancel, zero_add]
    _ = _ := by ring

/-- The explicit coordinate equivalence between the two actual principal localizations. -/
def mobiusEquiv (h2 : (2 : K) ≠ 0) : tRing K ≃ₐ[K] uRing K := by
  refine AlgEquiv.ofAlgHom (tToU K h2) (uToT K h2) ?_ ?_
  · apply IsLocalization.algHom_ext (Submonoid.powers (uDenominator K))
    apply Polynomial.algHom_ext
    change tToU K h2 (uToT K h2 (u K)) = u K
    rw [uToT_u, tToU_uAtT]
  · apply IsLocalization.algHom_ext (Submonoid.powers (tDenominator K))
    apply Polynomial.algHom_ext
    change uToT K h2 (tToU K h2 (t K)) = t K
    rw [tToU_t, uToT_tAtU]

end
end ManuscriptAudit.NodalSmoothMobius

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalSmoothMobius.uAtT_times_tplus,
      ``ManuscriptAudit.NodalSmoothMobius.tAtU_times_uminus,
      ``ManuscriptAudit.NodalSmoothMobius.uToT_u,
      ``ManuscriptAudit.NodalSmoothMobius.tToU_t,
      ``ManuscriptAudit.NodalSmoothMobius.mobiusEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
