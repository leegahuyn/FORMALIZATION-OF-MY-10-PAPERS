import Lean.Elab.Tactic.Omega
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.NormNum

namespace PrimalitySheafVerification.ManuscriptAudit

/-- Paper 4, physical PDF p. 134, with p=p₂=3, A=4, n=2, y=3, m=1 and the
positive sign in M=p₂y+(A−1). The displayed Y=A^(p₂) uses the second prime.
Paper 1, physical PDF p. 8, gives Sⱼ(A)=choose(A+1,j). -/
def paper4RemarkPhi (j : ℕ) : ℚ :=
  (((3 * 3 + (4 - 1)) * Nat.choose (4 + 1) j : ℕ) : ℚ) /
    ((Nat.gcd j.factorial 1 : ℚ) * (4 : ℚ) ^ 3)

private theorem paper4_value_scaled (e a : ℕ) (ha : ¬ 3 ∣ a) (ha₀ : a ≠ 0) :
    padicValRat 3 (((3 : ℚ) ^ e * (a : ℚ)) / (4 : ℚ) ^ 3) = (e : ℤ) := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h₃ : padicValRat 3 (3 : ℚ) = 1 := padicValRat.self (by decide)
  have h₄ : padicValRat 3 (4 : ℚ) = 0 := by
    change padicValRat 3 ((4 : ℕ) : ℚ) = 0
    simp only [padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd (by decide : ¬ (3 : ℕ) ∣ 4), Nat.cast_zero]
  have hunit : padicValRat 3 (a : ℚ) = 0 := by
    simp only [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd ha, Nat.cast_zero]
  have hpow₃ : (3 : ℚ) ^ e ≠ 0 := pow_ne_zero _ (by norm_num)
  have hcast : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ha₀
  have hpow₄ : (4 : ℚ) ^ 3 ≠ 0 := pow_ne_zero _ (by norm_num)
  simp only [padicValRat.div (p := 3) (mul_ne_zero hpow₃ hcast) hpow₄,
    padicValRat.mul (p := 3) hpow₃ hcast, padicValRat.pow (p := 3) (3 : ℚ),
    padicValRat.pow (p := 3) (4 : ℚ), h₃, h₄, hunit,
    mul_one, mul_zero, add_zero, sub_zero]

/-- Both individual normalized terms have valuation one, and the sum with
coefficients a₀=a₁=1 has valuation two. -/
theorem paper4_remark8_2_3_cancellation :
    padicValRat 3 (paper4RemarkPhi 0) = 1 ∧
      padicValRat 3 (paper4RemarkPhi 1) = 1 ∧
      padicValRat 3 (paper4RemarkPhi 0 + paper4RemarkPhi 1) = 2 := by
  have h₀ : paper4RemarkPhi 0 = (12 : ℚ) / (4 : ℚ) ^ 3 := by
    norm_num [paper4RemarkPhi, show Nat.choose (4 + 1) 0 = 1 from by decide,
      show Nat.gcd (Nat.factorial 0) 1 = 1 from by decide]
  have h₁ : paper4RemarkPhi 1 = (60 : ℚ) / (4 : ℚ) ^ 3 := by
    norm_num [paper4RemarkPhi, show Nat.choose (4 + 1) 1 = 5 from by decide,
      show Nat.gcd (Nat.factorial 1) 1 = 1 from by decide]
  have he₀ : paper4RemarkPhi 0 = ((3 : ℚ) ^ 1 * ((4 : ℕ) : ℚ)) / (4 : ℚ) ^ 3 := by
    norm_num [h₀]
  have he₁ : paper4RemarkPhi 1 = ((3 : ℚ) ^ 1 * ((20 : ℕ) : ℚ)) / (4 : ℚ) ^ 3 := by
    norm_num [h₁]
  have hes : paper4RemarkPhi 0 + paper4RemarkPhi 1 =
      ((3 : ℚ) ^ 2 * ((8 : ℕ) : ℚ)) / (4 : ℚ) ^ 3 := by
    norm_num [h₀, h₁]
  exact ⟨he₀.symm ▸ paper4_value_scaled 1 4 (by decide) (by decide),
    he₁.symm ▸ paper4_value_scaled 1 20 (by decide) (by decide),
    hes.symm ▸ paper4_value_scaled 2 8 (by decide) (by decide)⟩

/-- The reverse implication of Remark 8.2.3 fails even for the displayed
expansion with integer F₂=10, a₀=2 and a₁=−1. Here X=100, Y=64
and u=(X−Y)/Y=9/16, which has valuation two while (H₂) fails. -/
theorem paper4_remark8_2_3_refutation :
    let Y := (4 : ℚ) ^ 3
    let X := (10 : ℚ) * (Nat.choose (4 + 1) 2 : ℚ)
    Y = X + 2 * 12 * (Nat.choose (4 + 1) 0 : ℚ) / (Nat.gcd (Nat.factorial 0) 1 : ℚ)
      + (-1) * 12 * (Nat.choose (4 + 1) 1 : ℚ) / (Nat.gcd (Nat.factorial 1) 1 : ℚ) ∧
    ¬ ((∀ j : ℕ, j < 2 → (2 : ℤ) ≤ padicValRat 3 (paper4RemarkPhi j)) ↔
      (2 : ℤ) ≤ padicValRat 3 ((X - Y) / Y)) := by
  dsimp only
  have hchoose : Nat.choose (4 + 1) 2 = 10 := by decide
  refine ⟨?_, ?_⟩
  · norm_num [hchoose, show Nat.choose (4 + 1) 0 = 1 from by decide,
      show Nat.choose (4 + 1) 1 = 5 from by decide,
      show Nat.gcd (Nat.factorial 0) 1 = 1 from by decide,
      show Nat.gcd (Nat.factorial 1) 1 = 1 from by decide]
  · have hu : ((10 : ℚ) * (Nat.choose (4 + 1) 2 : ℚ) - (4 : ℚ) ^ 3) /
        (4 : ℚ) ^ 3 =
        (9 : ℚ) / 16 := by
      norm_num [hchoose]
    have hscale : (9 : ℚ) / 16 = ((3 : ℚ) ^ 2 * ((4 : ℕ) : ℚ)) / (4 : ℚ) ^ 3 := by
      norm_num
    have hval : padicValRat 3 ((9 : ℚ) / 16) = 2 :=
      hscale.symm ▸ paper4_value_scaled 2 4 (by decide) (by decide)
    intro heq
    have hgood : (2 : ℤ) ≤ padicValRat 3
        (((10 : ℚ) * (Nat.choose (4 + 1) 2 : ℚ) - (4 : ℚ) ^ 3) /
          (4 : ℚ) ^ 3) := by
      simp only [hu, hval, le_refl]
    have hbad := heq.mpr hgood 0 (by decide)
    rw [paper4_remark8_2_3_cancellation.1] at hbad
    exact (by decide : ¬ (2 : ℤ) ≤ 1) hbad

/-- Paper 6, physical pp. 193 and 197. The LTE identity fails with
A=1+3⁰=2 and j=1 at the permitted endpoint T=0. -/
theorem paper6_lte_T_zero_refutation :
    let A : ℤ := 1 + (3 : ℤ) ^ 0
    padicValInt 3 (A ^ ((3 : ℕ) ^ 1) - 1) = 0 ∧
      padicValInt 3 (A - 1) + 1 = 1 ∧
      padicValInt 3 (A ^ ((3 : ℕ) ^ 1) - 1) ≠ padicValInt 3 (A - 1) + 1 := by
  dsimp only
  have h₁ : (1 + (3 : ℤ) ^ 0) ^ ((3 : ℕ) ^ 1) - 1 = 7 := by norm_num
  have h₂ : (1 + (3 : ℤ) ^ 0) - 1 = 1 := by norm_num
  have h₇ : padicValInt 3 (7 : ℤ) = 0 :=
    padicValInt.eq_zero_of_not_dvd (by decide)
  simp [h₁, h₂, h₇, padicValInt.one]

/-- Paper 1, p. 8, equation (7). At p=p₂=3, n=2, A=10 and y=1,
the plus-sign modulus is 12 and has order one. The printed minimum is two. -/
theorem paper1_indexed_ultrametric_estimate_refutation :
    Nat.nth Nat.Prime 1 = 3 ∧ Nat.Coprime 10 3 ∧
      padicValRat 3 ((3 : ℚ) * 1 + (10 - 1)) <
        min (2 + padicValRat 3 (1 : ℚ)) (padicValRat 3 (10 - 1 : ℚ)) := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨Nat.nth_prime_one_eq_three, by decide, ?_⟩
  have h₃ : padicValRat 3 (3 : ℚ) = 1 := padicValRat.self (by decide)
  have h₄ : padicValRat 3 (4 : ℚ) = 0 := by
    change padicValRat 3 ((4 : ℕ) : ℚ) = 0
    simp only [padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd (by decide : ¬ (3 : ℕ) ∣ 4), Nat.cast_zero]
  have h₁ : padicValRat 3 (1 : ℚ) = 0 := by simp
  have hM : padicValRat 3 ((3 : ℚ) * 1 + (10 - 1)) = 1 := by
    rw [show (3 : ℚ) * 1 + (10 - 1) = 3 * 4 by norm_num,
      padicValRat.mul (p := 3) (by norm_num : (3 : ℚ) ≠ 0) (by norm_num : (4 : ℚ) ≠ 0),
      h₃, h₄, add_zero]
  have hA : padicValRat 3 (10 - 1 : ℚ) = 2 := by
    rw [show (10 - 1 : ℚ) = (3 : ℚ) ^ 2 by norm_num, padicValRat.pow (p := 3), h₃]
    norm_num
  rw [hM, h₁, hA]
  decide

/-- Paper 1, p. 10, Proposition 2.4(b). For p=p₂=3, A=10,
n=2, t=2, and σ=3, the displayed plus-branch residue class is 2 modulo
3. Every member of that class misses divisibility by 27. -/
theorem paper1_indexed_prime_design_congruence_fails (y : ℤ) (hy : y % 3 = 2) :
    ¬ (3 : ℤ) ^ (3 : ℕ) ∣ 3 * y + (10 - 1) := by
  change ¬ (27 : ℤ) ∣ 3 * y + 9
  rintro ⟨z, hz⟩
  omega

/-- The actual congruence class at the same indexed-prime profile. -/
theorem paper1_indexed_prime_design_actual_congruence (y : ℤ) :
    (3 : ℤ) ^ (3 : ℕ) ∣ 3 * y + (10 - 1) ↔ y % 9 = 6 := by
  change (27 : ℤ) ∣ 3 * y + 9 ↔ y % 9 = 6
  constructor
  · rintro ⟨z, hz⟩
    omega
  · intro hy
    refine ⟨y / 9 + 1, ?_⟩
    omega

/-- For the genuine prime-power modulus, the high-valuation branch is
exactly a single congruence at the reduced exponent. The offset may carry
either sign. -/
theorem paper1_power_modulus_congruence {p b u y : ℤ} (hp : p ≠ 0)
    {n t σ : ℕ} (ht : n ≤ t) (hσ : n ≤ σ) (hb : b = p ^ t * u) :
    p ^ σ ∣ p ^ n * y + b ↔ p ^ (σ - n) ∣ y + p ^ (t - n) * u := by
  have hσ' : p ^ n * p ^ (σ - n) = p ^ σ := by
    rw [← pow_add, Nat.add_sub_of_le hσ]
  have ht' : p ^ n * p ^ (t - n) = p ^ t := by
    rw [← pow_add, Nat.add_sub_of_le ht]
  calc
    p ^ σ ∣ p ^ n * y + b ↔ p ^ n * p ^ (σ - n) ∣ p ^ n * (y + p ^ (t - n) * u) := by
      rw [hσ', mul_add, ← mul_assoc, ht', ← hb]
    _ ↔ _ := mul_dvd_mul_iff_left (pow_ne_zero n hp)

/-- The printed conclusion about the low-valuation branch holds with a genuine
power modulus and a unit coefficient in the offset. -/
theorem paper1_power_modulus_low_branch {p b u : ℤ} (hp : p ≠ 0)
    {n t : ℕ} (ht : t < n) (hb : b = p ^ t * u) (hu : ¬ p ∣ u) (y : ℤ) :
    p ^ t ∣ p ^ n * y + b ∧ ¬ p ^ (t + 1) ∣ p ^ n * y + b := by
  have hn : p ^ t * p ^ (n - t) = p ^ n := by
    rw [← pow_add, Nat.add_sub_of_le ht.le]
  have hM : p ^ n * y + b = p ^ t * (p ^ (n - t) * y + u) := by
    rw [hb, mul_add, ← mul_assoc, hn]
  rw [hM]
  refine ⟨dvd_mul_right _ _, ?_⟩
  intro h
  rw [pow_succ] at h
  have hz : p ∣ p ^ (n - t) * y + u := (mul_dvd_mul_iff_left (pow_ne_zero t hp)).mp h
  have hpow : p ∣ p ^ (n - t) := by
    simpa only [pow_one] using pow_dvd_pow p (Nat.succ_le_of_lt (Nat.sub_pos_of_lt ht))
  have hsub := dvd_sub hz (dvd_mul_of_dvd_left hpow y)
  exact hu (by simpa only [add_sub_cancel_left] using hsub)

/-- A high-valuation power modulus can be chosen to equal the requested
power exactly, avoiding zero at any finite threshold. -/
theorem paper1_power_modulus_exact_design {p b u : ℤ} {n t σ : ℕ}
    (ht : n ≤ t) (hσ : n ≤ σ) (hb : b = p ^ t * u) :
    ∃ y : ℤ, p ^ n * y + b = p ^ σ := by
  have hσ' : p ^ n * p ^ (σ - n) = p ^ σ := by
    rw [← pow_add, Nat.add_sub_of_le hσ]
  have ht' : p ^ n * p ^ (t - n) = p ^ t := by
    rw [← pow_add, Nat.add_sub_of_le ht]
  refine ⟨p ^ (σ - n) - p ^ (t - n) * u, ?_⟩
  rw [hb, mul_sub, hσ', ← mul_assoc, ht', sub_add_cancel]

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``paper4_remark8_2_3_cancellation, ``paper4_remark8_2_3_refutation,
      ``paper6_lte_T_zero_refutation, ``paper1_indexed_ultrametric_estimate_refutation,
      ``paper1_indexed_prime_design_congruence_fails,
      ``paper1_indexed_prime_design_actual_congruence,
      ``paper1_power_modulus_congruence, ``paper1_power_modulus_low_branch,
      ``paper1_power_modulus_exact_design] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"

end PrimalitySheafVerification.ManuscriptAudit

