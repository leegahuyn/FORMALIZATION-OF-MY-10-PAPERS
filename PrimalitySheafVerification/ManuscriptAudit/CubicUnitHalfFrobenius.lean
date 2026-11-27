import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.CubicExplicitHalfTranslation
import PrimalitySheafVerification.ManuscriptAudit.CubicHalfFrobeniusSigns
import PrimalitySheafVerification.ManuscriptAudit.CubicFiniteFieldProduct
import PrimalitySheafVerification.ManuscriptAudit.CubicSplitTwoPowerFrobenius

/-! Apply the exact square-root sign calculation to the actual reference cubic with A=1. -/

namespace ManuscriptAudit.CubicUnitHalfFrobenius

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate CubicTwoTorsion
open CubicThreeTorsionCard CubicCubeRotation CubicRotationQuadratic
open CubicExplicitHalfTorsion CubicExplicitHalfTranslation CubicHalfFrobeniusSigns
open CubicNonsplitThreeAdicTrace CubicSplitTwoPowerFrobenius

noncomputable section

private theorem rotate_root {L : Type*} [Field L] [DecidableEq L] {A a b u : L}
    (hu : u ^ 3 = 1) (hΔ : (shortCubic (0 : L) A).Δ ≠ 0)
    (ha : a ^ 3 + A = 0) (hb : b ^ 3 + A = 0) (he : u * a = b) :
    rotate u hu hΔ (rootPoint hΔ ha) = rootPoint hΔ hb := by
  unfold rootPoint
  rw [rotate_some, Affine.Point.some.injEq]
  exact ⟨he, rfl⟩

variable (K L : Type*) [Field K] [Fintype K] [DecidableEq K]
  [Field L] [IsAlgClosed L] [DecidableEq L] [Algebra K L]

/-- An explicit geometric four-torsion point on the reference cubic determines the
Frobenius sign by the quadratic character of the first root difference. -/
theorem exists_half_frobenius {z : K} (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (hz : IsPrimitiveRoot z 3) (hq : Fintype.card K % 4 = 3) :
    let G := GeometricPoints K L (1 : K)
    let R := geometricRotation K L h₂ h₃ (one_ne_zero : (1 : K) ≠ 0) hz
    let F := arithmeticPointFrobenius K L (1 : K)
    ∃ T P : G, T ≠ 0 ∧ T ≠ R T ∧ (2 : ℕ) • T = 0 ∧ (2 : ℕ) • P = T ∧
      F P = quadraticChar K (z - 1) • P + R T := by
  let i := algebraMap K L
  let A := i (1 : K)
  let u := i z
  let a : L := -1
  let b := -u
  let c := -(u ^ 2)
  have hA : A = 1 := map_one i
  have hA₀ : A ≠ 0 := by rw [hA]; exact one_ne_zero
  have h₂L : (2 : L) ≠ 0 := by simpa only [map_ofNat] using (map_ne_zero i).mpr h₂
  have h₃L : (3 : L) ≠ 0 := by simpa only [map_ofNat] using (map_ne_zero i).mpr h₃
  have hchar : ringChar K ≠ 2 := by
    intro h
    exact h₂ ((ringChar.spec K 2).mpr (by simpa only [h] using (dvd_rfl : (2 : ℕ) ∣ 2)))
  have hu : IsPrimitiveRoot u 3 := hz.map_of_injective i.injective
  have hu₁ : u ≠ 1 := hu.ne_one (by decide)
  have hu₂ : u ^ 2 ≠ 1 := hu.pow_ne_one_of_pos_of_lt (by decide) (by decide)
  have hcu : u ^ 2 + u + 1 = 0 := CubicFiniteFieldProduct.cube_root_relation hu
  have hpow₆ : u ^ 6 = 1 := by
    rw [show (6 : ℕ) = 3 * 2 by decide, pow_mul, hu.pow_eq_one, one_pow]
  have hΔ := shortCubic_discriminant_ne_zero h₂L h₃L hA₀
  have ha : a ^ 3 + A = 0 := by rw [hA]; dsimp only [a]; ring
  have hb : b ^ 3 + A = 0 := by rw [hA]; dsimp only [b]; linear_combination -hu.pow_eq_one
  have hc : c ^ 3 + A = 0 := by rw [hA]; dsimp only [c]; linear_combination -hpow₆
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (i (z - 1)) (by decide : 0 < (2 : ℕ))
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (i (z ^ 2 - 1)) (by decide : 0 < (2 : ℕ))
  have hr' : r ^ 2 = u - 1 := by simpa only [u, map_sub, map_one] using hr
  have hs' : s ^ 2 = u ^ 2 - 1 := by simpa only [u, map_sub, map_pow, map_one] using hs
  have hSum : r ^ 2 + s ^ 2 = 3 * a := by
    rw [hr', hs']
    dsimp only [a]
    linear_combination hcu
  have hProd : (r * s) ^ 2 = 3 * a ^ 2 := by
    rw [mul_pow, hr', hs']
    dsimp only [a]
    linear_combination hu.pow_eq_one - hcu
  have hr₀ : r ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hr'
    exact hu₁ (sub_eq_zero.mp hr'.symm)
  have hs₀ : s ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hs'
    exact hu₂ (sub_eq_zero.mp hs'.symm)
  have hPlus : r + s ≠ 0 := by
    intro h
    have he : r ^ 2 = s ^ 2 := by rw [eq_neg_of_add_eq_zero_left h, neg_sq]
    rw [hr', hs'] at he
    have hpow : u ^ 1 = u ^ 2 := by simpa only [pow_one] using sub_right_cancel he
    exact (by decide : (1 : ℕ) ≠ 2) (hu.pow_inj (by decide) (by decide) hpow)
  let T := rootPoint hΔ ha
  let P := halfPoint hΔ ha hSum hProd
  let R := geometricRotation K L h₂ h₃ (one_ne_zero : (1 : K) ≠ 0) hz
  let g := FiniteField.frobeniusAlgHom K L
  let F := arithmeticPointFrobenius K L (1 : K)
  have hDouble : (2 : ℕ) • P = T := double_half h₂L hΔ ha hSum hProd
    (mul_ne_zero hr₀ hs₀) hPlus
  have hT₂ : (2 : ℕ) • T = 0 := by
    unfold T rootPoint
    exact (two_nsmul_affine_some_iff h₂L _).mpr rfl
  have hTne : T ≠ 0 := by
    intro h
    unfold T rootPoint at h
    cases h
  have hR₁ : R T = rootPoint hΔ hb := by
    exact rotate_root hu.pow_eq_one hΔ ha hb (by dsimp only [a, b]; ring)
  have hR₂ : R (R T) = rootPoint hΔ hc := by
    rw [hR₁]
    exact rotate_root hu.pow_eq_one hΔ hb hc (by dsimp only [b, c]; ring)
  have hTdist : T ≠ R T := by
    intro h
    rw [hR₁] at h
    have he := congrArg (abscissa (A := A)) h
    simp only [T, rootPoint, abscissa_some, a, b] at he
    exact hu₁ (neg_injective he.symm)
  have haFix : g a = a := by
    dsimp only [a]
    rw [map_neg, map_one]
  have hrF : g r = i (quadraticChar K (z - 1) : K) * r := frobenius_sqrt K L hchar hr
  have hsF : g s = i (quadraticChar K (z ^ 2 - 1) : K) * s := frobenius_sqrt K L hchar hs
  have hp := difference_signs K hz hq
  refine ⟨T, P, hTne, hTdist, hT₂, hDouble, ?_⟩
  rcases quadraticChar_dichotomy (sub_ne_zero.mpr (hz.ne_one (by decide))) with h | h
  · have hrF' : g r = r := by
      simpa only [h, Int.cast_one, map_one, one_mul] using hrF
    have hsF' : g s = -s := by
      simpa only [hp, h, Int.cast_neg, Int.cast_one, map_neg, map_one, neg_one_mul] using hsF
    have hm := native_map_half K L g 1 hΔ ha haFix hSum hProd
      (by simpa [neg_sq] using hSum) (by simpa [mul_neg, neg_sq] using hProd) hrF' hsF'
    change F P = _ at hm
    rw [h, one_zsmul, hR₁]
    exact hm.trans (add_root_eq_flip_s hΔ ha hb hSum hProd
      (by rw [hr']; dsimp only [a, b]; ring) hr₀ hPlus).symm
  · have hrF' : g r = -r := by
      simpa only [h, Int.cast_neg, Int.cast_one, map_neg, map_one, neg_one_mul] using hrF
    have hsF' : g s = s := by
      simpa only [hp, h, neg_neg, Int.cast_one, map_one, one_mul] using hsF
    have hm := native_map_half K L g 1 hΔ ha haFix hSum hProd
      (by simpa [neg_sq] using hSum) (by simpa [neg_mul, neg_sq] using hProd) hrF' hsF'
    change F P = _ at hm
    have he := hm.trans (add_root_eq_flip_r hΔ ha hc hSum hProd
      (by rw [hs']; dsimp only [a, c]; ring) hs₀ hPlus).symm
    have hqR : R (R T) + R T + T = 0 :=
      rotate_sum_eq_zero h₂L h₃L hA₀ hu.pow_eq_one hu₁ hΔ T
    have hRneg : -R T = R T := by
      have ht : R T + R T = 0 := by rw [← map_add, ← two_nsmul, hT₂, map_zero]
      exact (eq_neg_of_add_eq_zero_left ht).symm
    have hRsub : R (R T) = -R T - T := by
      have he' : R (R T) + (R T + T) = 0 := by simpa only [← add_assoc] using hqR
      rw [eq_neg_of_add_eq_zero_left he', neg_add_rev]
      abel
    rw [← hR₂] at he
    rw [h, neg_one_zsmul]
    refine he.trans ?_
    rw [hRsub, hRneg, ← hDouble, two_nsmul]
    abel

end
end ManuscriptAudit.CubicUnitHalfFrobenius

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicUnitHalfFrobenius.exists_half_frobenius
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
