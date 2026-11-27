import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper3CompositeGates

/-!
# Arbitrarily large composite inputs passing the explicit local predicates

Physical PDF pp. 53, 60–62 and 82. Vary the permitted integer base
along one progression and keep the same depth, residue, and elliptic
discriminant tests as the explicit composite witnesses.
-/

namespace ManuscriptAudit.Paper3UnboundedCompositeGates

open WeierstrassCurve Paper3CompositeGates

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

def base (n : ℕ) : ℕ := 6*n + 23

def passesAtBase (A r : ℕ) (c : ℝ) : Prop :=
  let Y := A^r
  let X := Y + 3
  (A : ℝ) ^ (-c * (r : ℝ)) ≤ |(X : ℝ) - (Y : ℝ)| ∧
  |(X : ℝ) - (Y : ℝ)| ≤ (A : ℝ) / (r : ℝ) ∧
  (∃ y : ℤ, (2 : ℤ) = (r : ℤ) * y - ((A : ℤ) - 1)) ∧
  2 ∣ X ∧
  padicValNat 3 Y + 1 ≤ padicValNat 3 (X - Y) ∧
  (testCurve.map (Int.castRingHom (ZMod 3))).IsElliptic ∧
  Nat.Coprime 2 3

theorem base_twenty_three_specialization (r : ℕ) (c : ℝ) :
    passesAtBase (base 0) r c ↔ Paper3CompositeGates.passes r c := by
  rfl

theorem all_progression_bases_pass (n : ℕ) (c : ℝ) (hc : 1 < c)
    {r : ℕ} (hr : r = 3 ∨ r = 6) :
    passesAtBase (base n) r c ∧ ¬ (base n ^ r + 3).Prime := by
  have hr0 : 0 < r := by omega
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr0
  have hA : 23 ≤ base n := by unfold base; omega
  have hAR : (23 : ℝ) ≤ base n := by exact_mod_cast hA
  have hWin : (3 : ℝ) ≤ (base n : ℝ) / (r : ℝ) := by
    apply (le_div_iff₀ hrR).2
    rcases hr with rfl | rfl <;> norm_num <;> linarith
  have hLow : (base n : ℝ) ^ (-c * (r : ℝ)) ≤ 3 := by
    have hc0 : 0 < c := by linarith
    exact (Real.rpow_lt_one_of_one_lt_of_neg (by linarith : (1 : ℝ) < base n)
      (mul_neg_of_neg_of_pos (neg_neg_of_pos hc0) hrR)).le.trans (by norm_num)
  have hMod : ∃ y : ℤ, (2 : ℤ) = (r : ℤ) * y - ((base n : ℤ) - 1) := by
    rcases hr with rfl | rfl
    · refine ⟨2*(n : ℤ)+8, ?_⟩
      push_cast [base]
      ring
    · refine ⟨(n : ℤ)+4, ?_⟩
      push_cast [base]
      ring
  have hA2 : base n % 2 = 1 := by unfold base; omega
  have hY2 : (base n ^ r) % 2 = 1 := by rw [Nat.pow_mod, hA2, one_pow]; decide
  have hEven : 2 ∣ base n ^ r + 3 := by
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  have hA3 : ¬ 3 ∣ base n := by rw [Nat.dvd_iff_mod_eq_zero, base]; omega
  have hY3 : ¬ 3 ∣ base n ^ r := fun h => hA3 ((by decide : Nat.Prime 3).dvd_of_dvd_pow h)
  have hVal : padicValNat 3 (base n ^ r) = 0 := padicValNat.eq_zero_of_not_dvd hY3
  have hDist : |((base n ^ r + 3 : ℕ) : ℝ) - ((base n ^ r : ℕ) : ℝ)| = 3 := by
    push_cast
    norm_num
  constructor
  · simp only [passesAtBase]
    rw [hDist, hVal, show base n ^ r + 3 - base n ^ r = 3 by omega, padicValNat_self]
    exact ⟨hLow, hWin, hMod, hEven, le_rfl, discriminant_good, by decide⟩
  · intro hPrime
    rcases (Nat.dvd_prime hPrime).mp hEven with h | h <;> omega

theorem unbounded_composites_in_both_exponent_readings (B : ℕ) (c : ℝ) (hc : 1 < c)
    {r : ℕ} (hr : r = 3 ∨ r = 6) :
    ∃ A X : ℕ, B ≤ X ∧ X = A^r + 3 ∧ passesAtBase A r c ∧ ¬ X.Prime := by
  obtain ⟨hPass,hComp⟩ := all_progression_bases_pass B c hc hr
  have hA0 : 0 < base B := by unfold base; omega
  have hPow : base B ≤ base B ^ r := by
    simpa only [pow_one] using Nat.pow_le_pow_right hA0 (show 1 ≤ r by omega)
  have hB : B ≤ base B := by unfold base; omega
  exact ⟨base B, base B ^ r + 3, by omega, rfl, hPass, hComp⟩

end ManuscriptAudit.Paper3UnboundedCompositeGates

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper3UnboundedCompositeGates.base_twenty_three_specialization,
      ``ManuscriptAudit.Paper3UnboundedCompositeGates.all_progression_bases_pass,
      ``ManuscriptAudit.Paper3UnboundedCompositeGates.unbounded_composites_in_both_exponent_readings] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
