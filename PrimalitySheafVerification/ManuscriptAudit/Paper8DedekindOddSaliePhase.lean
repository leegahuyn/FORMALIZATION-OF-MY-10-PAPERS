import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8DedekindOddPhaseCRT
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossPoincareKernel

/-! Exact unit phase times a Jacobi-twisted additive summand for every odd denominator. -/

namespace ManuscriptAudit.Paper8DedekindOddSaliePhase

open Paper8ContourResidueWeights Paper8DedekindKloostermanCongruence Paper8DedekindOddPhaseCRT
open Paper8OddCrossPoincareKernel

noncomputable section

private theorem expPhase_add (z w : ℂ) :
    exponentialPhase (z + w) = exponentialPhase z * exponentialPhase w := by
  unfold exponentialPhase
  rw [mul_add, Complex.exp_add]

private theorem expPhase_int (m : ℤ) : exponentialPhase (m : ℂ) = 1 := by
  unfold exponentialPhase
  rw [mul_comm, Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow]

private theorem expPhase_div_eq_of_dvd_sub {D : ℕ} (hD : 0 < D) (a b : ℤ)
    (h : (D : ℤ) ∣ a - b) :
    exponentialPhase ((a : ℂ) / (D : ℂ)) = exponentialPhase ((b : ℂ) / (D : ℂ)) := by
  obtain ⟨m, hm⟩ := h
  have hC : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hMC := congrArg (fun n : ℤ => (n : ℂ)) hm
  push_cast at hMC
  have hEq : (a : ℂ) / (D : ℂ) = (b : ℂ) / (D : ℂ) + (m : ℂ) := by
    field_simp [hC]
    linear_combination hMC
  rw [hEq, expPhase_add, expPhase_int, mul_one]

private theorem bezout_odd_right {M c : ℕ} (hM : M % 2 = 1) {u v : ℤ}
    (h : (4 * (c : ℤ)) * u + (M : ℤ) * v = 1) : (2 : ℤ) ∣ v - 1 := by
  have hm : (M : ZMod 2) = 1 := by
    change (M : ZMod 2) = ((1 : ℕ) : ZMod 2)
    exact (ZMod.natCast_eq_natCast_iff' M 1 2).2 (by simpa using hM)
  have hz := congrArg (fun z : ℤ => (z : ZMod 2)) h
  push_cast at hz
  have hv : (v : ZMod 2) = 1 := by
    simpa only [hm, show (4 : ZMod 2) = 0 by decide, zero_mul, one_mul, zero_add] using hz
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).1
  push_cast
  rw [hv, sub_self]

private theorem expPhase_quadratic_sign (χ v : ℤ) (hχ : χ = 1 ∨ χ = -1) (hv : (2 : ℤ) ∣ v - 1) :
    exponentialPhase ((v : ℂ) * ((χ : ℂ) - 1) / 4) = (χ : ℂ) := by
  rcases hχ with rfl | rfl
  · norm_num [exponentialPhase]
  · obtain ⟨m, hm⟩ := hv
    have hz := congrArg (fun z : ℤ => (z : ℂ)) hm
    push_cast at hz
    have hEq : (v : ℂ) * (((-1 : ℤ) : ℂ) - 1) / 4 =
        (1 : ℂ) / 2 + (((-m - 1 : ℤ) : ℂ)) := by
      push_cast
      linear_combination -(1 / 2 : ℂ) * hz
    rw [hEq, expPhase_add, expPhase_int, mul_one]
    unfold exponentialPhase
    push_cast
    rw [show 2 * (Real.pi : ℂ) * Complex.I * ((1 : ℂ) / 2) =
      (Real.pi : ℂ) * Complex.I by ring, Complex.exp_pi_mul_I]

private theorem phase_factor {h k M c : ℕ} (hk : 0 < k) (hc : 0 < c)
    (hM0 : 0 < M) (hM : M % 2 = 1) (hC : h.Coprime k)
    (hDenom : 4 * c * M = 24 * k) (u v a : ℤ)
    (hBez : (4 * (c : ℤ)) * u + (M : ℤ) * v = 1)
    (hSmall : (4 * (c : ℤ)) ∣ dedekindPhaseNumerator h k - dedekindPhaseNumerator 1 k -
      (c : ℤ) * (jacobiSym (h : ℤ) k - 1))
    (hBig : (M : ℤ) ∣ dedekindPhaseNumerator h k - ((h : ℤ) + a)) :
    Complex.exp ((Real.pi : ℂ) * Complex.I * ((dedekindSum (h : ℤ) k : ℝ) : ℂ)) =
      exponentialPhase (((v * dedekindPhaseNumerator 1 k : ℤ) : ℂ) / (4 * (c : ℂ))) *
        (jacobiSym (h : ℤ) k : ℂ) *
        exponentialPhase (((u * ((h : ℤ) + a) : ℤ) : ℂ) / (M : ℂ)) := by
  let N := dedekindPhaseNumerator h k
  let B := dedekindPhaseNumerator 1 k
  let χ := jacobiSym (h : ℤ) k
  let d := 4 * c
  have hd : 0 < d := Nat.mul_pos (by decide) hc
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hMZ : (M : ℂ) ≠ 0 := by exact_mod_cast hM0.ne'
  have hχ : χ = 1 ∨ χ = -1 := jacobiSym.eq_one_or_neg_one (by
    simpa only [Int.gcd_natCast_natCast] using hC.gcd_eq_one)
  have hN : (N : ℂ) = 12 * (k : ℂ) * ((dedekindSum (h : ℤ) k : ℝ) : ℂ) := by
    have hr := (dedekind_phase_numerator_spec hk hC).1
    have hh := congrArg (fun x : ℚ => (x : ℂ)) hr
    push_cast at hh ⊢
    exact hh
  have hE : Complex.exp ((Real.pi : ℂ) * Complex.I * ((dedekindSum (h : ℤ) k : ℝ) : ℂ)) =
      exponentialPhase ((N : ℂ) / (24 * (k : ℂ))) := by
    unfold exponentialPhase
    rw [hN]
    congr 1
    field_simp [hk0] <;> ring
  have hBezC := congrArg (fun n : ℤ => (n : ℂ)) hBez
  have hDenomC := congrArg (fun n : ℕ => (n : ℂ)) hDenom
  push_cast at hBezC hDenomC
  have hSplit : (N : ℂ) / (24 * (k : ℂ)) =
      (((v * N : ℤ) : ℂ) / (4 * (c : ℂ))) + (((u * N : ℤ) : ℂ) / (M : ℂ)) := by
    rw [← hDenomC]
    calc
      _ = ((4 * (c : ℂ)) * (u : ℂ) + (M : ℂ) * (v : ℂ)) * (N : ℂ) /
          (4 * (c : ℂ) * (M : ℂ)) := by rw [hBezC, one_mul]
      _ = _ := by push_cast; field_simp [hc0, hMZ] <;> ring
  have hSm : (d : ℤ) ∣ v * N - (v * B + v * (c : ℤ) * (χ - 1)) := by
    obtain ⟨q, hq⟩ := hSmall
    have hD : (d : ℤ) = (4 * (c : ℤ)) := by unfold d; push_cast <;> rfl
    rw [hD]
    refine ⟨v * q, ?_⟩
    change N - B - (c : ℤ) * (χ - 1) = (4 * (c : ℤ)) * q at hq
    linear_combination v * hq
  have hBg : (M : ℤ) ∣ u * N - u * ((h : ℤ) + a) := by
    obtain ⟨q, hq⟩ := hBig
    refine ⟨u * q, ?_⟩
    change N - ((h : ℤ) + a) = (M : ℤ) * q at hq
    linear_combination u * hq
  have hSmPh := expPhase_div_eq_of_dvd_sub hd _ _ hSm
  have hdC : (d : ℂ) = 4 * (c : ℂ) := by unfold d; push_cast <;> rfl
  rw [hdC] at hSmPh
  have hCorr : (((v * B + v * (c : ℤ) * (χ - 1) : ℤ) : ℂ) / (4 * (c : ℂ))) =
      (((v * B : ℤ) : ℂ) / (4 * (c : ℂ))) + (v : ℂ) * ((χ : ℂ) - 1) / 4 := by
    push_cast
    field_simp [hc0] <;> ring
  have hSig := expPhase_quadratic_sign χ v hχ (bezout_odd_right hM hBez)
  rw [hE, hSplit, expPhase_add, expPhase_div_eq_of_dvd_sub hM0 _ _ hBg, hSmPh, hCorr,
    expPhase_add, hSig]

theorem dedekind_odd_coprime_six_summand {h k : ℕ} (hh : h % 2 = 1) (hk : k % 2 = 1)
    (h3 : ¬ (3 : ℕ) ∣ k) (hC : h.Coprime k) (u v a : ℤ)
    (hBez : 24 * u + (k : ℤ) * v = 1) (ha : (h : ZMod k) * (a : ZMod k) = 1) :
    Complex.exp ((Real.pi : ℂ) * Complex.I * ((dedekindSum (h : ℤ) k : ℝ) : ℂ)) =
      exponentialPhase (((v * dedekindPhaseNumerator 1 k : ℤ) : ℂ) / 24) *
        (jacobiSym (h : ℤ) k : ℂ) *
        exponentialPhase (((u * ((h : ℤ) + a) : ℤ) : ℂ) / (k : ℂ)) := by
  have hk0 : 0 < k := by omega
  let H := ZMod.unitOfCoprime h hC
  have hA' : (H : ZMod k) * (a : ZMod k) = 1 := ha
  have hA : (a : ZMod k) = ((H⁻¹ : (ZMod k)ˣ) : ZMod k) := by
    calc
      _ = ((H⁻¹ : (ZMod k)ˣ) : ZMod k) * ((H : ZMod k) * (a : ZMod k)) := by
        rw [Units.inv_mul_cancel_left]
      _ = _ := by rw [hA', mul_one]
  have hBig : (k : ℤ) ∣ dedekindPhaseNumerator h k - ((h : ℤ) + a) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ k).1
    push_cast
    rw [hA, (dedekind_phase_numerator_spec hk0 hC).2.1, sub_self]
  simpa only [Nat.cast_ofNat, show (4 : ℂ) * 6 = 24 by norm_num] using
    (phase_factor (M := k) (c := 6) hk0 (by decide) hk0 hk hC (by norm_num) u v a
      (by norm_num at hBez ⊢; exact hBez)
      (by norm_num; exact phase_odd_baseline_mod_twentyFour hh hk h3 hC) hBig)

theorem dedekind_odd_multiple_three_summand {h k : ℕ} (hh : h % 2 = 1) (hk : k % 2 = 1)
    (h3 : (3 : ℕ) ∣ k) (hC : h.Coprime k) (u v a : ℤ)
    (hBez : 8 * u + (3 * (k : ℤ)) * v = 1) (ha : (h : ZMod (3 * k)) * (a : ZMod (3 * k)) = 1) :
    Complex.exp ((Real.pi : ℂ) * Complex.I * ((dedekindSum (h : ℤ) k : ℝ) : ℂ)) =
      exponentialPhase (((v * dedekindPhaseNumerator 1 k : ℤ) : ℂ) / 8) *
        (jacobiSym (h : ℤ) k : ℂ) *
        exponentialPhase (((u * ((h : ℤ) + a) : ℤ) : ℂ) / (3 * (k : ℂ))) := by
  have hk0 : 0 < k := by omega
  have hM : (3 * k) % 2 = 1 := by
    rw [Nat.mul_mod, hk]
  have hBig : ((3 * k : ℕ) : ℤ) ∣ dedekindPhaseNumerator h k - ((h : ℤ) + a) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ (3 * k)).1
    push_cast
    rw [phase_numerator_congr_mod_three_mul hk0 h3 hC a ha, sub_self]
  simpa only [Nat.cast_mul, Nat.cast_ofNat, show (4 : ℂ) * 2 = 8 by norm_num] using
    (phase_factor (M := 3 * k) (c := 2) hk0 (by decide) (Nat.mul_pos (by decide) hk0) hM hC
      (by ring) u v a
      (by push_cast; norm_num at hBez ⊢; exact hBez)
      (by norm_num; exact phase_odd_baseline_mod_eight hh hk hC) hBig)

end
end ManuscriptAudit.Paper8DedekindOddSaliePhase

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8DedekindOddSaliePhase.dedekind_odd_coprime_six_summand,
      ``ManuscriptAudit.Paper8DedekindOddSaliePhase.dedekind_odd_multiple_three_summand] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
