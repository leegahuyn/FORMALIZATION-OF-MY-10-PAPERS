import Lean.Util.CollectAxioms
import Mathlib.Data.Nat.Factorization.Induction
import PrimalitySheafVerification.ManuscriptAudit.Paper8JacobiLocalSquareRoot

/-! Exact CRT assembles the local bounds into the manuscript's composite cross-sum bound. -/

namespace ManuscriptAudit.Paper8OddCrossCompositeBound

open Finset Paper8JacobiLocalSquareRoot Paper8JacobiWeightCRT
open Paper8OddCrossJacobiSum Paper8ZModAdditiveCRT Paper8OddCrossCuspRows Paper8OddCrossCuspCutoff
open Paper8DedekindKloostermanCongruence Paper8OddCrossPoincareKernel

noncomputable section

private def CompositeBound (n : ℕ) : Prop :=
  n.Coprime 2 → ∀ [NeZero n] (a : ZMod n), IsUnit a →
    ‖twistedSymmetricUnitSum (jacobiUnitWeight n) a‖ ≤
      (2 : ℝ) ^ n.primeFactors.card * Real.sqrt (n : ℝ)

private theorem isUnit_factor_term {R : Type*} [CommMonoid R] {u v : R} (h : u * v = 1) :
    IsUnit u :=
  ⟨⟨u, v, h, by simpa only [mul_comm] using h⟩, rfl⟩

theorem crt_local_coefficient_units {n m : ℕ} {u v a : ℤ}
    (hBez : u * (m : ℤ) + v * (n : ℤ) = 1) (ha : IsUnit (a : ZMod (n * m))) :
    IsUnit ((u * a : ℤ) : ZMod n) ∧ IsUnit ((v * a : ℤ) : ZMod m) := by
  have hu : IsUnit (u : ZMod n) := by
    have h := congrArg (fun x : ℤ => (x : ZMod n)) hBez
    push_cast at h
    have h' : (u : ZMod n) * (m : ZMod n) = 1 := by
      simpa only [ZMod.natCast_self, mul_zero, add_zero] using h
    exact isUnit_factor_term h'
  have hv : IsUnit (v : ZMod m) := by
    have h := congrArg (fun x : ℤ => (x : ZMod m)) hBez
    push_cast at h
    have h' : (v : ZMod m) * (n : ZMod m) = 1 := by
      simpa only [ZMod.natCast_self, mul_zero, zero_add] using h
    exact isUnit_factor_term h'
  have hna : IsUnit (a : ZMod n) := by
    simpa only [map_intCast] using ha.map (ZMod.castHom (dvd_mul_right n m) (ZMod n))
  have hma : IsUnit (a : ZMod m) := by
    simpa only [map_intCast] using ha.map (ZMod.castHom (dvd_mul_left m n) (ZMod m))
  rw [Int.cast_mul, Int.cast_mul]
  exact ⟨hu.mul hna, hv.mul hma⟩

private theorem compositeBound_all (n : ℕ) : CompositeBound n := by
  refine Nat.recOnPosPrimePosCoprime (motive := CompositeBound) ?_ ?_ ?_ ?_ n
  · intro p r hP hr hC _ a ha
    letI : Fact p.Prime := ⟨hP⟩
    have hp2 : p ≠ 2 := by
      have hc : p.Coprime 2 := Nat.Coprime.of_dvd_left (by
        obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
        refine ⟨p ^ s, ?_⟩
        rw [hs, pow_succ, mul_comm]) hC
      intro he
      have hd : p ∣ 2 := ⟨1, by simpa only [mul_one] using he.symm⟩
      exact ((hP.coprime_iff_not_dvd).1 hc) hd
    have h := norm_jacobi_sum_prime_power hp2 hr a ha
    simpa only [Nat.primeFactors_prime_pow hr.ne' hP, Finset.card_singleton, pow_one] using h
  · intro _ h0
    exact (h0.out rfl).elim
  · intro _ _ a _
    letI : Unique ((ZMod 1)ˣ) := { default := 1, uniq := fun _ => Subsingleton.elim _ _ }
    have hTerm (x : (ZMod 1)ˣ) : jacobiUnitWeight 1 x *
        ZMod.stdAddChar (a * ((x : ZMod 1) + ((x⁻¹ : (ZMod 1)ˣ) : ZMod 1))) = 1 := by
      rw [show a * ((x : ZMod 1) + ((x⁻¹ : (ZMod 1)ˣ) : ZMod 1)) = 0 from Subsingleton.elim _ _,
        AddChar.map_zero_eq_one]
      simp [jacobiUnitWeight, jacobiSym.one_right]
    simp [twistedSymmetricUnitSum, hTerm]
  · intro n m hn hm hC ihN ihM hTwo _ a ha
    letI : NeZero n := ⟨by omega⟩
    letI : NeZero m := ⟨by omega⟩
    let u := Nat.gcdB n m
    let v := Nat.gcdA n m
    have hBez : u * (m : ℤ) + v * (n : ℤ) = 1 := by
      have h := Nat.gcd_eq_gcd_ab n m
      change (Nat.gcd n m : ℤ) = (n : ℤ) * v + (m : ℤ) * u at h
      rw [hC.gcd_eq_one, Nat.cast_one] at h
      linear_combination -h
    obtain ⟨A, rfl⟩ := ZMod.intCast_surjective a
    obtain ⟨hA, hB⟩ := crt_local_coefficient_units hBez ha
    have hN2 : n.Coprime 2 := Nat.Coprime.of_dvd_left (dvd_mul_right n m) hTwo
    have hM2 : m.Coprime 2 := Nat.Coprime.of_dvd_left (dvd_mul_left m n) hTwo
    rw [jacobiTwistedUnitSum_chineseRemainder hC u v A hBez, norm_mul]
    calc
      _ ≤ ((2 : ℝ) ^ n.primeFactors.card * Real.sqrt (n : ℝ)) *
          ((2 : ℝ) ^ m.primeFactors.card * Real.sqrt (m : ℝ)) :=
        mul_le_mul (ihN hN2 _ hA) (ihM hM2 _ hB) (norm_nonneg _) (by positivity)
      _ = _ := by
        rw [hC.primeFactors_mul, Finset.card_union_of_disjoint hC.disjoint_primeFactors, pow_add,
          Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg n)]
        ring

theorem norm_jacobi_sum_odd_modulus {n : ℕ} [NeZero n] (h2 : n.Coprime 2)
    (a : ZMod n) (ha : IsUnit a) :
    ‖twistedSymmetricUnitSum (jacobiUnitWeight n) a‖ ≤
      (2 : ℝ) ^ n.primeFactors.card * Real.sqrt (n : ℝ) :=
  compositeBound_all n h2 a ha

theorem norm_oddCrossSum_coprime_six {n : ℕ} [NeZero n] (hC : n.Coprime 6) :
    ‖crossSum (Nat.pos_of_ne_zero (NeZero.ne n))‖ ≤
      (2 : ℝ) ^ n.primeFactors.card * Real.sqrt (n : ℝ) := by
  let u := Nat.gcdA 24 n
  let v := Nat.gcdB 24 n
  have h2 : n.Coprime 2 := Nat.Coprime.of_dvd_right (by decide : 2 ∣ 6) hC
  have h3 : n.Coprime 3 := Nat.Coprime.of_dvd_right (by decide : 3 ∣ 6) hC
  have h2N := (Nat.prime_two.coprime_iff_not_dvd).1 h2.symm
  have h3N := (Nat.prime_three.coprime_iff_not_dvd).1 h3.symm
  have hOdd : n % 2 = 1 := by
    have hN : n % 2 ≠ 0 := fun h => h2N (Nat.dvd_of_mod_eq_zero h)
    omega
  have h24 : (24 : ℕ).Coprime n := by
    apply Nat.Coprime.symm
    rw [show (24 : ℕ) = 2 ^ 3 * 3 by decide, Nat.coprime_mul_iff_right]
    exact ⟨h2.pow_right 3, h3⟩
  have hBez : 24 * u + (n : ℤ) * v = 1 := by
    have h := Nat.gcd_eq_gcd_ab 24 n
    change (Nat.gcd 24 n : ℤ) = 24 * u + (n : ℤ) * v at h
    rw [h24.gcd_eq_one, Nat.cast_one] at h
    exact h.symm
  have hU : IsUnit (u : ZMod n) := by
    have h := congrArg (fun s : ℤ => (s : ZMod n)) hBez
    push_cast at h
    have h' : (24 : ZMod n) * (u : ZMod n) = 1 := by
      simpa only [ZMod.natCast_self, zero_mul, add_zero] using h
    exact isUnit_factor_term (by simpa only [mul_comm] using h')
  let A := v * dedekindPhaseNumerator 1 n
  have hPhase : exponentialPhase ((A : ℂ) / 24) = ZMod.stdAddChar (A : ZMod 24) := by
    rw [exponentialPhase, ZMod.stdAddChar_coe]
    congr 1
    ring
  have hNorm : ‖exponentialPhase ((A : ℂ) / 24)‖ = 1 := by
    rw [hPhase]
    have h := Complex.norm_eq_one_of_mem_rootsOfUnity
      ((ZMod.stdAddChar (N := 24)).val_mem_rootsOfUnity (A : ZMod 24) (by
        rw [ZMod.ringChar_zmod_n]; decide))
    simpa only [IsUnit.unit_spec] using h
  have hChi : ‖(chiFour (n : ZMod 4) : ℂ)‖ ≤ 1 := by
    unfold chiFour
    split_ifs <;> norm_num
  rw [crossSum_eq_jacobi_unit_sum hOdd h3N u v hBez, norm_mul, norm_mul]
  change ‖(chiFour (n : ZMod 4) : ℂ)‖ * ‖exponentialPhase ((A : ℂ) / 24)‖ * _ ≤ _
  rw [hNorm, mul_one]
  exact (mul_le_of_le_one_left (norm_nonneg _) hChi).trans (norm_jacobi_sum_odd_modulus h2 _ hU)

end
end ManuscriptAudit.Paper8OddCrossCompositeBound

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8OddCrossCompositeBound.norm_jacobi_sum_odd_modulus,
      ``ManuscriptAudit.Paper8OddCrossCompositeBound.norm_oddCrossSum_coprime_six] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
