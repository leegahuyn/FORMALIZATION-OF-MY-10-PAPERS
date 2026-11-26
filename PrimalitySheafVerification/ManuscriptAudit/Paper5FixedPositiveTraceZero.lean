import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.Paper5FixedTraceZero

/-!
# A fixed positive-parameter Paper 5 model with trace zero

The model `y² = x³ - 11x + 14` has prime coefficient `pₙ = 11` and positive
constant `A = 14` coprime to it. The point-count proof uses the quadratic
character transport between the two standard cubic equations for a
degree-two isogeny. It proves the transport directly by counting the
fibers of `x ↦ x + b/x` over a finite field.
-/

namespace ManuscriptAudit.Paper5FixedPositiveTraceZero

open scoped BigOperators

noncomputable section

section CharacterTransport

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private def sourceCubic (a b x : F) : F := x ^ 3 + a * x ^ 2 + b * x

private def partnerCubic (a b x : F) : F := x ^ 3 - 2 * a * x ^ 2 + (a ^ 2 - 4 * b) * x

private abbrev QuadRoots (t b : F) := {x : F // x ^ 2 - t * x + b = 0}

private def quadRootEquiv (h2 : (2 : F) ≠ 0) (t b : F) :
    QuadRoots t b ≃ {y : F // y ^ 2 = t ^ 2 - 4 * b} where
  toFun x := ⟨2 * (x : F) - t, by linear_combination (4 : F) * x.2⟩
  invFun y := ⟨((y : F) + t) / 2, by
    field_simp [h2]
    linear_combination y.2⟩
  left_inv x := by
    apply Subtype.ext
    change ((2 * (x : F) - t) + t) / 2 = (x : F)
    rw [sub_add_cancel]
    exact (div_eq_iff h2).2 (mul_comm _ _)
  right_inv y := by
    apply Subtype.ext
    change 2 * (((y : F) + t) / 2) - t = (y : F)
    rw [mul_comm (2 : F), div_mul_cancel₀ _ h2, add_sub_cancel_right]

private theorem quadRoot_ne_zero {t b : F} (hb : b ≠ 0) (x : QuadRoots t b) :
    (x : F) ≠ 0 := by
  intro h
  exact hb (by simpa [h] using x.2)

private def parameterEquiv (b : F) (hb : b ≠ 0) :
    {x : F // x ≠ 0} ≃ (Σ t : F, QuadRoots t b) where
  toFun x := ⟨(x : F) + b / (x : F), ⟨x, by
    rw [add_mul, div_mul_cancel₀ _ x.2]
    ring⟩⟩
  invFun z := ⟨z.2, quadRoot_ne_zero hb z.2⟩
  left_inv x := Subtype.ext rfl
  right_inv := by
    rintro ⟨t, ⟨x, hx⟩⟩
    have hne : x ≠ 0 := quadRoot_ne_zero hb (⟨x, hx⟩ : QuadRoots t b)
    have he : x + b / x = t := by
      apply (mul_right_cancel₀ hne)
      rw [add_mul, div_mul_cancel₀ _ hne]
      linear_combination hx
    subst t
    rfl

private theorem character_nonzero_x (a b : F) (x : {x : F // x ≠ 0}) :
    quadraticChar F (sourceCubic a b x) =
      quadraticChar F ((x : F) + b / (x : F) + a) := by
  have hpoly : sourceCubic a b x = (x : F) ^ 2 * ((x : F) + b / (x : F) + a) := by
    unfold sourceCubic
    calc
      (x : F) ^ 3 + a * (x : F) ^ 2 + b * (x : F) =
          (x : F) ^ 2 * ((x : F) + a) + (x : F) * (b / (x : F) * (x : F)) := by
        rw [div_mul_cancel₀ _ x.2]
        ring
      _ = _ := by ring
  rw [hpoly, map_mul, quadraticChar_sq_one' x.2, one_mul]

/-- The standard degree-two partner cubics have the same quadratic-character sum.
The proof only uses the cardinalities of the quadratic fibers. -/
theorem quadratic_partner_character_sum (h2 : (2 : F) ≠ 0) (hchar : ringChar F ≠ 2)
    (a b : F) (hb : b ≠ 0) :
    (∑ x : F, quadraticChar F (sourceCubic a b x)) =
      ∑ x : F, quadraticChar F (partnerCubic a b x) := by
  classical
  have hcard (t : F) : (Fintype.card (QuadRoots t b) : ℤ) =
      quadraticChar F (t ^ 2 - 4 * b) + 1 := by
    rw [Fintype.card_congr (quadRootEquiv h2 t b), ← Nat.card_eq_fintype_card]
    exact Paper5FixedTraceZero.square_fiber_card hchar (t ^ 2 - 4 * b)
  have hzero : (∑ t : F, quadraticChar F (t + a)) = 0 :=
    (Equiv.sum_comp (Equiv.addRight a) (fun t => quadraticChar F t)).trans
      (quadraticChar_sum_zero hchar)
  calc
    (∑ x : F, quadraticChar F (sourceCubic a b x)) =
        ∑ x : {x : F // x ≠ 0}, quadraticChar F ((x : F) + b / (x : F) + a) := by
      rw [Fintype.sum_eq_add_sum_subtype_ne _ (0 : F)]
      have hz : quadraticChar F (sourceCubic a b 0) = 0 := by simp [sourceCubic]
      rw [hz, zero_add]
      exact Finset.sum_congr rfl (fun x _ => character_nonzero_x a b x)
    _ = ∑ z : (Σ t : F, QuadRoots t b), quadraticChar F (z.1 + a) :=
      Equiv.sum_comp (parameterEquiv b hb) (fun z => quadraticChar F (z.1 + a))
    _ = ∑ t : F, (quadraticChar F (t ^ 2 - 4 * b) + 1) * quadraticChar F (t + a) := by
      rw [Fintype.sum_sigma]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    _ = (∑ t : F, quadraticChar F ((t + a) * (t ^ 2 - 4 * b))) +
          ∑ t : F, quadraticChar F (t + a) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t _
      rw [map_mul]
      ring
    _ = ∑ t : F, quadraticChar F ((t + a) * (t ^ 2 - 4 * b)) := by rw [hzero, add_zero]
    _ = ∑ x : F, quadraticChar F (partnerCubic a b x) := by
      rw [← Equiv.sum_comp (Equiv.addRight a) (fun x => quadraticChar F (partnerCubic a b x))]
      apply Finset.sum_congr rfl
      intro t _
      change quadraticChar F ((t + a) * (t ^ 2 - 4 * b)) =
        quadraticChar F (partnerCubic a b (t + a))
      congr 1
      unfold partnerCubic
      ring

end CharacterTransport

def fixedCurve : WeierstrassCurve ℤ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := -11
  a₆ := 14

def reduction (p : ℕ) : WeierstrassCurve (ZMod p) :=
  fixedCurve.map (Int.castRingHom (ZMod p))

theorem fixed_parameters : Nat.Prime 11 ∧ 5 ≤ (11 : ℕ) ∧ 0 < (14 : ℕ) ∧ Nat.Coprime 14 11 :=
  by decide

theorem fixedCurve_discriminant : fixedCurve.Δ = 512 := by
  norm_num [fixedCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem reduction_discriminant_ne_zero {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) :
    (reduction p).Δ ≠ 0 := by
  have hΔ : (reduction p).Δ = (Paper5FixedTraceZero.reduction p).Δ := by
    simp [reduction, fixedCurve_discriminant, Paper5FixedTraceZero.reduction,
      Paper5FixedTraceZero.fixedCurve_discriminant]
  rw [hΔ]
  exact Paper5FixedTraceZero.reduction_discriminant_ne_zero hp

private def baseCubic {F : Type*} [Ring F] (x : F) : F := x ^ 3 - x

private def targetCubic {F : Type*} [Ring F] (x : F) : F := x ^ 3 - 11 * x + 14

private theorem base_character_sum_zero {p : ℕ} [Fact p.Prime] (hr : p % 4 = 3) :
    (∑ x : ZMod p, quadraticChar (ZMod p) (baseCubic x)) = 0 := by
  have hns : ¬ IsSquare (-1 : ZMod p) := by
    simp [FiniteField.isSquare_neg_one_iff, ZMod.card, hr]
  have hχ : quadraticChar (ZMod p) (-1) = -1 :=
    quadraticChar_neg_one_iff_not_isSquare.mpr hns
  have hneg (x : ZMod p) :
      quadraticChar (ZMod p) (baseCubic (-x)) = -quadraticChar (ZMod p) (baseCubic x) := by
    have he : baseCubic (-x) = (-1) * baseCubic x := by unfold baseCubic; ring
    rw [he, map_mul, hχ, neg_one_mul]
  have hs : (∑ x : ZMod p, quadraticChar (ZMod p) (baseCubic (-x))) =
      ∑ x : ZMod p, quadraticChar (ZMod p) (baseCubic x) :=
    Equiv.sum_comp (Equiv.neg (ZMod p)) (fun x => quadraticChar (ZMod p) (baseCubic x))
  simp_rw [hneg, Finset.sum_neg_distrib] at hs
  omega

theorem target_character_sum_zero {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (hr : p % 4 = 3) :
    (∑ x : ZMod p, quadraticChar (ZMod p) (targetCubic x)) = 0 := by
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  have h2 := Paper5FixedTraceZero.two_ne_zero_zmod hp
  have hs (x : ZMod p) : sourceCubic (-3) 2 x = baseCubic (x + (-1)) := by
    unfold sourceCubic baseCubic
    ring
  have ht (x : ZMod p) : targetCubic x = partnerCubic (-3) 2 (x + (-2)) := by
    unfold targetCubic partnerCubic
    ring
  calc
    (∑ x : ZMod p, quadraticChar (ZMod p) (targetCubic x)) =
        ∑ x : ZMod p, quadraticChar (ZMod p) (partnerCubic (-3) 2 x) := by
      simp_rw [ht]
      exact Equiv.sum_comp (Equiv.addRight (-2 : ZMod p))
        (fun x => quadraticChar (ZMod p) (partnerCubic (-3) 2 x))
    _ = ∑ x : ZMod p, quadraticChar (ZMod p) (sourceCubic (-3) 2 x) :=
      (quadratic_partner_character_sum h2 hchar (-3) 2 h2).symm
    _ = ∑ x : ZMod p, quadraticChar (ZMod p) (baseCubic x) := by
      simp_rw [hs]
      exact Equiv.sum_comp (Equiv.addRight (-1 : ZMod p))
        (fun x => quadraticChar (ZMod p) (baseCubic x))
    _ = 0 := base_character_sum_zero hr

private abbrev Solutions (p : ℕ) :=
  Σ x : ZMod p, {y : ZMod p // y ^ 2 = targetCubic x}

private theorem solution_count {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (hr : p % 4 = 3) :
    Nat.card (Solutions p) = p := by
  classical
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  have hc (x : ZMod p) : (Fintype.card {y : ZMod p // y ^ 2 = targetCubic x} : ℤ) =
      quadraticChar (ZMod p) (targetCubic x) + 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact Paper5FixedTraceZero.square_fiber_card hchar (targetCubic x)
  have hc' : (Fintype.card (Solutions p) : ℤ) = (p : ℤ) := by
    unfold Solutions
    rw [Fintype.card_sigma, Nat.cast_sum]
    simp only [hc, Finset.sum_add_distrib, target_character_sum_zero hp hr, zero_add]
    simp [ZMod.card]
  rw [Nat.card_eq_fintype_card]
  exact_mod_cast hc'

private theorem reduction_nonsingular_iff {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (x y : ZMod p) :
    (reduction p).toProjective.toAffine.Nonsingular x y ↔ y ^ 2 = targetCubic x := by
  rw [← WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero
    (reduction_discriminant_ne_zero hp), WeierstrassCurve.Affine.equation_iff]
  simp [reduction, fixedCurve, targetCubic, sub_eq_add_neg]

private def projectiveEquiv {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) :
    (reduction p).toProjective.Point ≃ Option (Solutions p) := by
  let W := (reduction p).toProjective
  let e₁ : W.Point ≃ W.toAffine.Point :=
    (WeierstrassCurve.Projective.Point.toAffineAddEquiv (W := W)).toEquiv
  let e₂ : W.toAffine.Point ≃ Option {xy : ZMod p × ZMod p // W.toAffine.Nonsingular xy.1 xy.2} :=
    W.toAffine.nonsingularPointEquiv
  let e₃ : {xy : ZMod p × ZMod p // W.toAffine.Nonsingular xy.1 xy.2} ≃ Solutions p :=
    { toFun := fun xy => ⟨xy.1.1, ⟨xy.1.2, (reduction_nonsingular_iff hp _ _).1 xy.2⟩⟩
      invFun := fun z => ⟨(z.1, z.2.1), (reduction_nonsingular_iff hp _ _).2 z.2.2⟩
      left_inv := by rintro ⟨⟨x, y⟩, h⟩; rfl
      right_inv := by rintro ⟨x, ⟨y, h⟩⟩; rfl }
  exact e₁.trans (e₂.trans e₃.optionCongr)

theorem projective_count {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (hr : p % 4 = 3) :
    Nat.card (reduction p).toProjective.Point = p + 1 := by
  classical
  calc
    Nat.card (reduction p).toProjective.Point = Nat.card (Option (Solutions p)) :=
      Nat.card_congr (projectiveEquiv hp)
    _ = Nat.card (Solutions p) + 1 := by simp only [Nat.card_eq_fintype_card, Fintype.card_option]
    _ = p + 1 := by rw [solution_count hp hr]

def arithmeticTrace (p : ℕ) : ℤ :=
  (p : ℤ) + 1 - (Nat.card (reduction p).toProjective.Point : ℤ)

theorem arithmeticTrace_eq_zero {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (hr : p % 4 = 3) :
    arithmeticTrace p = 0 := by
  unfold arithmeticTrace
  rw [projective_count hp hr]
  simp

theorem arbitrarily_large_good_trace_zero_primes (N : ℕ) :
    ∃ p : ℕ, N < p ∧ p.Prime ∧ 14 < p ∧ p % 4 = 3 ∧
      (reduction p).Δ ≠ 0 ∧ arithmeticTrace p = 0 := by
  obtain ⟨p, hb, hp, hr⟩ := Paper5FixedTraceZero.arbitrarily_large_primes_three_mod_four (max N 14)
  have hp₁₄ : 14 < p := (le_max_right N 14).trans_lt hb
  have hp₅ : 5 ≤ p := by omega
  letI : Fact p.Prime := ⟨hp⟩
  exact ⟨p, (le_max_left N 14).trans_lt hb, hp, hp₁₄, hr,
    reduction_discriminant_ne_zero hp₅, arithmeticTrace_eq_zero hp₅ hr⟩

end

end ManuscriptAudit.Paper5FixedPositiveTraceZero

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.Paper5FixedPositiveTraceZero.quadratic_partner_character_sum,
      ``ManuscriptAudit.Paper5FixedPositiveTraceZero.fixed_parameters,
      ``ManuscriptAudit.Paper5FixedPositiveTraceZero.fixedCurve_discriminant,
      ``ManuscriptAudit.Paper5FixedPositiveTraceZero.projective_count,
      ``ManuscriptAudit.Paper5FixedPositiveTraceZero.arithmeticTrace_eq_zero,
      ``ManuscriptAudit.Paper5FixedPositiveTraceZero.arbitrarily_large_good_trace_zero_primes] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
