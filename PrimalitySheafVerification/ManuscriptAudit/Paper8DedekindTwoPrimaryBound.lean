import Lean.Util.CollectAxioms
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import PrimalitySheafVerification.ManuscriptAudit.Paper8DedekindTwoPrimaryData
import PrimalitySheafVerification.ManuscriptAudit.Paper8TwoPrimaryStationaryBound
import PrimalitySheafVerification.ManuscriptAudit.Paper8UnitReductionThree

/-! Unit-group formulation and square-root bound for the actual Dedekind two-primary factor. -/

namespace ManuscriptAudit.Paper8DedekindTwoPrimaryBound

open Finset Paper8DedekindTwoPrimaryData Paper8TwoPrimaryStationaryBound Paper8UnitReductionThree
open Paper8ProductStationaryPhase Paper8KloostermanProductPhase Paper8KloostermanDigitSum
open scoped Classical

noncomputable section

def twoPrimaryUnitSum {M : ℕ} [NeZero M] (hd : 8 ∣ M) (e n : ℕ) (a b : ZMod M) : ℂ :=
  ∑ x : (ZMod M)ˣ, twoPrimaryCharacter e n (ZMod.castHom hd (ZMod 8) (x : ZMod M)) *
    kloostermanPhase a b (x : ZMod M)

private theorem norm_kloostermanPhase {M : ℕ} [NeZero M] (a b x : ZMod M) :
    ‖kloostermanPhase a b x‖ = 1 := by
  unfold kloostermanPhase
  have hP : 0 < ringChar (ZMod M) := by
    rw [ZMod.ringChar_zmod_n]
    exact Nat.pos_of_ne_zero (NeZero.ne _)
  have h := Complex.norm_eq_one_of_mem_rootsOfUnity
    ((ZMod.stdAddChar (N := M)).val_mem_rootsOfUnity (a * x + b * x⁻¹) hP)
  simpa only [IsUnit.unit_spec] using h

theorem norm_twoPrimaryUnitSum_trivial {M : ℕ} [NeZero M] (hd : 8 ∣ M) (e n : ℕ) (a b : ZMod M) :
    ‖twoPrimaryUnitSum hd e n a b‖ ≤ (M : ℝ) := by
  unfold twoPrimaryUnitSum
  rw [sum_units_as_indicator (fun x : ZMod M =>
    twoPrimaryCharacter e n (ZMod.castHom hd (ZMod 8) x) * kloostermanPhase a b x)]
  calc
    _ ≤ ∑ x : ZMod M, ‖if IsUnit x then twoPrimaryCharacter e n (ZMod.castHom hd (ZMod 8) x) *
          kloostermanPhase a b x else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _x : ZMod M, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hx : IsUnit x
      · rw [if_pos hx, norm_mul, norm_kloostermanPhase, mul_one]
        exact norm_twoPrimaryCharacter_le e n _
      · simp [hx]
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]

theorem norm_twoPrimaryUnitSum_factored {M d r : ℕ} [NeZero M] [NeZero d]
    (hM : M = (2 * 2 ^ r) * (d * (2 * 2 ^ r))) (hd : 8 ∣ M) (hLow : 8 ∣ d * (2 * 2 ^ r))
    (e n : ℕ) (a b : ZMod M) (ha : IsUnit a) (hb : IsUnit b) :
    ‖twoPrimaryUnitSum hd e n a b‖ ≤ 4 * (d : ℝ) * ((2 * 2 ^ r : ℕ) : ℝ) := by
  subst M
  let h := 2 * 2 ^ r
  let m := d * h
  let M := h * m
  letI : NeZero h := ⟨mul_ne_zero (by decide) (pow_ne_zero _ (by decide))⟩
  let g := ZMod.castHom hLow (ZMod 8)
  let w (x : ZMod m) := twoPrimaryCharacter e n (g x)
  have hF : ZMod.castHom hd (ZMod 8) = g.comp (@reduceLowDigit h m) :=
    RingHom.ext_zmod _ _
  have hSum : twoPrimaryUnitSum hd e n a b = weightedKloostermanUnitSum w a b := by
    unfold twoPrimaryUnitSum
    rw [sum_units_as_indicator (fun x : ZMod M =>
      twoPrimaryCharacter e n (ZMod.castHom hd (ZMod 8) x) * kloostermanPhase a b x)]
    unfold weightedKloostermanUnitSum weightedKloostermanUnitTerm w
    simp only [hF, RingHom.comp_apply]
  rw [hSum]
  exact norm_weighted_kloosterman_two_primary r w (fun x => norm_twoPrimaryCharacter_le e n (g x)) a b ha hb

theorem norm_twoPrimaryUnitSum_squareRoot (e n : ℕ)
    (a b : ZMod (8 * 2 ^ e)) (ha : IsUnit a) (hb : IsUnit b) :
    letI : NeZero (2 ^ e) := ⟨pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0)⟩
    ‖twoPrimaryUnitSum (dvd_mul_right 8 (2 ^ e)) e n a b‖ ≤ 8 * Real.sqrt ((8 * 2 ^ e : ℕ) : ℝ) := by
  let R := 8 * 2 ^ e
  let h8 : 8 ∣ R := dvd_mul_right 8 (2 ^ e)
  letI : NeZero R := ⟨mul_ne_zero (by decide) (pow_ne_zero _ (by decide))⟩
  change ‖twoPrimaryUnitSum h8 e n a b‖ ≤ 8 * Real.sqrt (R : ℝ)
  by_cases he : e < 3
  · have hR : R ≤ 64 := by
      have hCases : e = 0 ∨ e = 1 ∨ e = 2 := by omega
      rcases hCases with h | h | h <;> norm_num [R, h]
    have hS : Real.sqrt (R : ℝ) ≤ 8 := by
      calc
        _ ≤ Real.sqrt (64 : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hR)
        _ = _ := by rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    calc
      _ ≤ (R : ℝ) := norm_twoPrimaryUnitSum_trivial h8 e n a b
      _ = Real.sqrt (R : ℝ) * Real.sqrt (R : ℝ) := by rw [← pow_two, Real.sq_sqrt (Nat.cast_nonneg R)]
      _ ≤ _ := mul_le_mul_of_nonneg_right hS (Real.sqrt_nonneg _)
  · let j := (e + 3) / 2
    have hj : 3 ≤ j := by dsimp only [j]; omega
    have hj0 : j ≠ 0 := by omega
    obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hj0
    let h := 2 * 2 ^ r
    let d : ℕ := if (e + 3) % 2 = 0 then 1 else 2
    have hd1 : 1 ≤ d := by unfold d; split_ifs <;> decide
    have hd2 : d ≤ 2 := by unfold d; split_ifs <;> decide
    letI : NeZero d := ⟨by omega⟩
    have hR : R = 2 ^ (e + 3) := by unfold R; rw [pow_add] <;> norm_num <;> ring
    have hh : h = 2 ^ j := by unfold h; rw [hr, pow_succ]; ring
    have hm : R = h * (d * h) := by
      by_cases hP : (e + 3) % 2 = 0
      · have hExp : e + 3 = j + j := by dsimp only [j]; omega
        rw [hR, hExp, pow_add]
        simp only [← hh, show d = 1 by simp [d, hP], one_mul]
      · have hExp : e + 3 = j + (1 + j) := by dsimp only [j]; omega
        rw [hR, hExp, pow_add, pow_add, pow_one]
        simp only [← hh, show d = 2 by simp [d, hP]]
    have hLow : 8 ∣ d * h := by
      have hD : 8 ∣ h := by rw [hh]; exact pow_dvd_pow 2 hj
      exact hD.trans (dvd_mul_left h d)
    have hS : (h : ℝ) ≤ Real.sqrt (R : ℝ) := by
      apply (Real.le_sqrt (Nat.cast_nonneg h) (Nat.cast_nonneg R)).2
      have hD : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
      rw [hm]
      push_cast
      nlinarith [mul_nonneg (sub_nonneg.mpr hD) (sq_nonneg (h : ℝ))]
    calc
      _ ≤ 4 * (d : ℝ) * (h : ℝ) := norm_twoPrimaryUnitSum_factored hm h8 hLow e n a b ha hb
      _ ≤ (8 : ℝ) * (h : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg h)
        have hD : (d : ℝ) ≤ 2 := by exact_mod_cast hd2
        linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hS (by norm_num)

end
end ManuscriptAudit.Paper8DedekindTwoPrimaryBound

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8DedekindTwoPrimaryBound.norm_twoPrimaryUnitSum_squareRoot
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
