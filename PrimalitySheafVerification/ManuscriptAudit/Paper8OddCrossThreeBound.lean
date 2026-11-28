import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossCompositeBound
import PrimalitySheafVerification.ManuscriptAudit.Paper8JacobiLiftWeight
import PrimalitySheafVerification.ManuscriptAudit.Paper8ExtraPrimeJacobi

/-! The actual three-divisible odd coefficient retains the composite square-root bound. -/

namespace ManuscriptAudit.Paper8OddCrossThreeBound

open Paper8OddCrossThreeSum Paper8JacobiLiftWeight Paper8ExtraPrimeJacobi Paper8ZModAdditiveCRT
open Paper8OddCrossJacobiSum Paper8OddCrossCompositeBound Paper8OddCrossCuspCutoff
open Paper8OddCrossCuspRows Paper8DedekindKloostermanCongruence Paper8OddCrossPoincareKernel

noncomputable section

private theorem extraPrimeJacobiSum_modulus_eq {M N : ℕ} [NeZero M] [NeZero N] (h : M = N)
    (a : ℤ) :
    twistedSymmetricUnitSum (extraPrimeJacobiUnitWeight 3 M) (a : ZMod M) =
      twistedSymmetricUnitSum (extraPrimeJacobiUnitWeight 3 N) (a : ZMod N) := by
  subst N
  rfl

private theorem unit_intCast_modulus_eq {M N : ℕ} (h : M = N) (a : ℤ) :
    IsUnit (a : ZMod M) ↔ IsUnit (a : ZMod N) := by subst N; rfl

theorem norm_jacobi_lift_sum {k : ℕ} [NeZero k] (hk2 : k.Coprime 2) (hk3 : 3 ∣ k)
    (a : ZMod (3 * k)) (ha : IsUnit a) :
    ‖twistedSymmetricUnitSum (jacobiLiftWeight k) a‖ ≤
      (2 : ℝ) ^ k.primeFactors.card * Real.sqrt ((3 * k : ℕ) : ℝ) := by
  let e := k.factorization 3
  let m := k / 3 ^ e
  let n := 3 ^ (e + 1)
  have he : 0 < e := Nat.prime_three.factorization_pos_of_dvd (NeZero.ne k) hk3
  have hD : 3 ^ e ∣ k := Nat.ordProj_dvd k 3
  have hK : 3 ^ e * m = k := Nat.mul_div_cancel' hD
  have hm : m ≠ 0 := fun hm0 => (NeZero.ne k) (by rw [← hK, hm0, mul_zero])
  have hm3 : ¬ 3 ∣ m := by
    unfold m
    rw [Nat.dvd_div_iff_mul_dvd hD, ← Nat.pow_succ]
    exact Nat.pow_succ_factorization_not_dvd (NeZero.ne k) Nat.prime_three
  have hC : n.Coprime m := (Nat.prime_three.coprime_iff_not_dvd.2 hm3).pow_left _
  have hC₀ : (3 ^ e).Coprime m := (Nat.prime_three.coprime_iff_not_dvd.2 hm3).pow_left _
  have hm2 : m.Coprime 2 := Nat.Coprime.of_dvd_left
    (show m ∣ k from ⟨3 ^ e, by rw [mul_comm, hK]⟩) hk2
  have hN : n * m = 3 * k := by unfold n; rw [pow_succ, ← hK]; ring
  have hn3 : 3 ∣ n := by unfold n; rw [pow_succ]; exact dvd_mul_left _ _
  letI : NeZero m := ⟨hm⟩
  letI : NeZero n := ⟨pow_ne_zero _ (by decide : (3 : ℕ) ≠ 0)⟩
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let u := Nat.gcdB n m
  let v := Nat.gcdA n m
  have hBez : u * (m : ℤ) + v * (n : ℤ) = 1 := by
    have h := Nat.gcd_eq_gcd_ab n m
    change (Nat.gcd n m : ℤ) = (n : ℤ) * v + (m : ℤ) * u at h
    rw [hC.gcd_eq_one, Nat.cast_one] at h
    linear_combination -h
  obtain ⟨A, rfl⟩ := ZMod.intCast_surjective a
  have hU : IsUnit (A : ZMod (n * m)) := (unit_intCast_modulus_eq hN A).2 ha
  obtain ⟨hU₁, hU₂⟩ := crt_local_coefficient_units hBez hU
  have hW : jacobiLiftWeight k = extraPrimeJacobiUnitWeight 3 (3 * k) :=
    funext (jacobiLiftWeight_eq_three_product (k := k))
  rw [hW, extraPrimeJacobiSum_modulus_eq hN.symm, extraPrimeJacobiSum_chineseRemainder hC hn3 u v A hBez, norm_mul]
  have hLocal : ‖twistedSymmetricUnitSum (extraPrimeJacobiUnitWeight 3 n) ((u * A : ℤ) : ZMod n)‖ ≤
      2 * Real.sqrt (n : ℝ) := norm_extraPrimeJacobiSum_prime_power (by decide : (3 : ℕ) ≠ 2) (by omega) _ hU₁
  have hOther := norm_jacobi_sum_odd_modulus hm2 ((v * A : ℤ) : ZMod m) hU₂
  calc
    _ ≤ (2 * Real.sqrt (n : ℝ)) * ((2 : ℝ) ^ m.primeFactors.card * Real.sqrt (m : ℝ)) :=
      mul_le_mul hLocal hOther (norm_nonneg _) (by positivity)
    _ = _ := by
      have hCard : k.primeFactors.card = 1 + m.primeFactors.card := by
        rw [← hK, hC₀.primeFactors_mul, Finset.card_union_of_disjoint hC₀.disjoint_primeFactors,
          Nat.primeFactors_prime_pow he.ne' Nat.prime_three, Finset.card_singleton]
      rw [hCard, pow_add, pow_one, ← hN, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg n)]
      ring

theorem norm_oddCrossSum_three_divides {k : ℕ} [NeZero k] (hk : k % 2 = 1) (hk3 : 3 ∣ k) :
    ‖crossSum (Nat.pos_of_ne_zero (NeZero.ne k))‖ ≤
      (2 : ℝ) ^ k.primeFactors.card * Real.sqrt (k : ℝ) := by
  have hk2 : k.Coprime 2 := by
    apply Nat.Coprime.symm
    apply Nat.prime_two.coprime_iff_not_dvd.2
    intro hd
    have ht := Nat.mod_eq_zero_of_dvd hd
    omega
  have hThreeTwo : (3 * k).Coprime 2 := by
    rw [Nat.coprime_mul_iff_left]
    exact ⟨by decide, hk2⟩
  have hEight : (8 : ℕ).Coprime (3 * k) := hThreeTwo.symm.pow_left 3
  let u := Nat.gcdA 8 (3 * k)
  let v := Nat.gcdB 8 (3 * k)
  have hBez : 8 * u + (3 * (k : ℤ)) * v = 1 := by
    have h := Nat.gcd_eq_gcd_ab 8 (3 * k)
    rw [hEight.gcd_eq_one] at h
    push_cast at h
    exact h.symm
  have hU : IsUnit (u : ZMod (3 * k)) := by
    have h := congrArg (fun s : ℤ => (s : ZMod (3 * k))) hBez
    have hZ : (3 : ZMod (3 * k)) * (k : ZMod (3 * k)) = 0 := by
      change ((3 : ℕ) : ZMod (3 * k)) * (k : ZMod (3 * k)) = 0
      rw [← Nat.cast_mul, ZMod.natCast_self]
    push_cast at h
    have hN : (8 : ZMod (3 * k)) * (u : ZMod (3 * k)) = 1 := by
      simpa only [hZ, zero_mul, add_zero] using h
    exact ⟨⟨u, 8, by simpa only [mul_comm] using hN, hN⟩, rfl⟩
  let A := v * dedekindPhaseNumerator 1 k
  have hPhase : exponentialPhase ((A : ℂ) / 8) = ZMod.stdAddChar (A : ZMod 8) := by
    rw [exponentialPhase, ZMod.stdAddChar_coe]
    congr 1
    ring
  have hNorm : ‖exponentialPhase ((A : ℂ) / 8)‖ = 1 := by
    rw [hPhase]
    have h := Complex.norm_eq_one_of_mem_rootsOfUnity
      ((ZMod.stdAddChar (N := 8)).val_mem_rootsOfUnity (A : ZMod 8) (by rw [ZMod.ringChar_zmod_n]; decide))
    simpa only [IsUnit.unit_spec] using h
  have hChi : ‖(chiFour (k : ZMod 4) : ℂ)‖ ≤ 1 := by
    unfold chiFour
    split_ifs <;> norm_num
  have hS : Real.sqrt ((3 * k : ℕ) : ℝ) ≤ 3 * Real.sqrt (k : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.sqrt_mul (by norm_num : 0 ≤ (3 : ℝ))]
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    rw [Real.sqrt_le_iff]
    norm_num
  rw [crossSum_eq_lifted_jacobi_sum hk hk3 u v hBez, norm_mul, norm_mul, norm_mul]
  change ‖(chiFour (k : ZMod 4) : ℂ)‖ * ‖(1 / 3 : ℂ)‖ * ‖exponentialPhase ((A : ℂ) / 8)‖ * _ ≤ _
  rw [hNorm, mul_one, norm_div, norm_one, Complex.norm_ofNat]
  calc
    _ ≤ (1 / 3 : ℝ) * ((2 : ℝ) ^ k.primeFactors.card * Real.sqrt ((3 * k : ℕ) : ℝ)) := by
      apply mul_le_mul _ (norm_jacobi_lift_sum hk2 hk3 _ hU) (norm_nonneg _) (by norm_num)
      exact mul_le_of_le_one_left (by norm_num) hChi
    _ ≤ (1 / 3 : ℝ) * ((2 : ℝ) ^ k.primeFactors.card * (3 * Real.sqrt (k : ℝ))) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hS (by positivity)) (by norm_num)
    _ = _ := by ring

end
end ManuscriptAudit.Paper8OddCrossThreeBound

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8OddCrossThreeBound.norm_oddCrossSum_three_divides
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
