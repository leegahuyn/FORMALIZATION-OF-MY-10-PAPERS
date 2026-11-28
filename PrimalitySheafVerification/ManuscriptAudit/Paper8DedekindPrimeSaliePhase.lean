import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Coprime.Basic
import PrimalitySheafVerification.ManuscriptAudit.Paper8DedekindPrimePhase
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossPoincareKernel

/-! An exact prime-modulus Dedekind exponential is a fixed unit phase times the corresponding Salié summand. -/

namespace ManuscriptAudit.Paper8DedekindPrimeSaliePhase

open Paper8ContourResidueWeights Paper8DedekindKloostermanCongruence Paper8DedekindPrimePhase
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

theorem phase_prime_baseline_mod_twentyFour {p h : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hp3 : ¬ (3 : ℕ) ∣ p) (hh : h % 2 = 1) (hC : h.Coprime p) :
    (24 : ℤ) ∣ dedekindPhaseNumerator h p - dedekindPhaseNumerator 1 p -
      6 * (1 - legendreSym p (h : ℤ)) := by
  let z := dedekindPhaseNumerator h p - dedekindPhaseNumerator 1 p - 6 * (1 - legendreSym p (h : ℤ))
  have hp0 := (Fact.out : p.Prime).pos
  have h1C : Nat.Coprime 1 p := Nat.coprime_one_left p
  have hDh := (dedekind_phase_numerator_spec hp0 hC).2.2.2 hp3
  have hD1 := (dedekind_phase_numerator_spec hp0 h1C).2.2.2 hp3
  have hThree : (3 : ℤ) ∣ z :=
    dvd_sub (dvd_sub hDh hD1) ⟨2 * (1 - legendreSym p (h : ℤ)), by ring⟩
  have hEight : (8 : ℤ) ∣ z := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd z 8).1
    unfold z
    push_cast
    rw [phase_mod_eight_legendre hp hh hC, phase_mod_eight_legendre hp (by decide) h1C]
    simp only [Int.cast_one, legendreSym.at_one]
    have h8 : (8 : ZMod 8) = 0 := by decide
    calc
      _ = (8 : ZMod 8) * (((legendreSym p (h : ℤ) : ℤ) : ZMod 8) - 1) := by ring
      _ = _ := by rw [h8, zero_mul]
  have hCop : IsCoprime (3 : ℤ) 8 := ⟨3, -1, by norm_num⟩
  simpa only [show (3 : ℤ) * 8 = 24 by norm_num] using hCop.mul_dvd hThree hEight

private theorem inverse_two_odd {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {u v : ℤ}
    (huv : 24 * u + (p : ℤ) * v = 1) : (2 : ℤ) ∣ v - 1 := by
  have hP : (p : ZMod 2) = 1 := by
    change (p : ZMod 2) = ((1 : ℕ) : ZMod 2)
    apply (ZMod.natCast_eq_natCast_iff' p 1 2).2
    simpa using (Nat.Prime.mod_two_eq_one_iff_ne_two (Fact.out : p.Prime)).2 hp
  have h := congrArg (fun n : ℤ => (n : ZMod 2)) huv
  push_cast at h
  have hV : (v : ZMod 2) = 1 := by
    simpa only [show (24 : ZMod 2) = 0 by decide, hP, zero_mul, one_mul, zero_add] using h
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).1
  push_cast
  rw [hV, sub_self]

private theorem expPhase_legendre_shift {p h : ℕ} [Fact p.Prime] (hC : h.Coprime p)
    (v : ℤ) (hv : (2 : ℤ) ∣ v - 1) :
    exponentialPhase (((v * (6 * (1 - legendreSym p (h : ℤ))) : ℤ) : ℂ) / 24) =
      (legendreSym p (h : ℤ) : ℂ) := by
  have hH : ((h : ℤ) : ZMod p) ≠ 0 := by
    push_cast
    exact (ZMod.unitOfCoprime h hC).ne_zero
  rcases legendreSym.eq_one_or_neg_one hH with h | h
  · rw [h]
    norm_num [exponentialPhase]
  · rw [h]
    have h24 : (24 : ℤ) ∣ v * (6 * (1 - (-1))) - 12 := by
      obtain ⟨m, hm⟩ := hv
      refine ⟨m, ?_⟩
      linear_combination 12 * hm
    rw [expPhase_div_eq_of_dvd_sub (D := 24) (by decide) _ 12 h24]
    unfold exponentialPhase
    push_cast
    rw [show 2 * (Real.pi : ℂ) * Complex.I * ((12 : ℂ) / 24) = (Real.pi : ℂ) * Complex.I by ring,
      Complex.exp_pi_mul_I]

theorem dedekind_prime_salie_summand {p h : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hp3 : ¬ (3 : ℕ) ∣ p) (hh : h % 2 = 1) (hC : h.Coprime p)
    (u v a : ℤ) (huv : 24 * u + (p : ℤ) * v = 1) (ha : (h : ZMod p) * (a : ZMod p) = 1) :
    Complex.exp ((Real.pi : ℂ) * Complex.I * ((dedekindSum (h : ℤ) p : ℝ) : ℂ)) =
      exponentialPhase (((v * dedekindPhaseNumerator 1 p : ℤ) : ℂ) / 24) *
        (legendreSym p (h : ℤ) : ℂ) *
        exponentialPhase (((u * ((h : ℤ) + a) : ℤ) : ℂ) / (p : ℂ)) := by
  let N := dedekindPhaseNumerator h p
  let N₁ := dedekindPhaseNumerator 1 p
  let χ := legendreSym p (h : ℤ)
  let H := ZMod.unitOfCoprime h hC
  have hp0 := (Fact.out : p.Prime).pos
  have hPC : (p : ℂ) ≠ 0 := by exact_mod_cast hp0.ne'
  obtain ⟨hN, hNp, _, _⟩ := dedekind_phase_numerator_spec hp0 hC
  have hA : (a : ZMod p) = ((H⁻¹ : (ZMod p)ˣ) : ZMod p) := by
    have hA' : (H : ZMod p) * (a : ZMod p) = 1 := ha
    calc
      _ = ((H⁻¹ : (ZMod p)ˣ) : ZMod p) * ((H : ZMod p) * (a : ZMod p)) := by
        rw [Units.inv_mul_cancel_left]
      _ = _ := by rw [hA', mul_one]
  have hpD : (p : ℤ) ∣ N - ((h : ℤ) + a) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1
    push_cast
    rw [hA, hNp, sub_self]
  have hU : (p : ℤ) ∣ u * N - u * ((h : ℤ) + a) := by
    obtain ⟨m, hm⟩ := hpD
    refine ⟨u * m, ?_⟩
    linear_combination u * hm
  have h24 := phase_prime_baseline_mod_twentyFour hp hp3 hh hC
  have hV : (24 : ℤ) ∣ v * N - (v * N₁ + v * (6 * (1 - χ))) := by
    obtain ⟨m, hm⟩ := h24
    refine ⟨v * m, ?_⟩
    change N - N₁ - 6 * (1 - χ) = 24 * m at hm
    linear_combination v * hm
  have hNX : (N : ℂ) = 12 * (p : ℂ) * ((dedekindSum (h : ℤ) p : ℝ) : ℂ) := by
    have h := congrArg (fun a : ℚ => (a : ℂ)) hN
    push_cast at h ⊢
    exact h
  have hB := congrArg (fun z : ℤ => (z : ℂ)) huv
  push_cast at hB
  have hSplit : (N : ℂ) / (24 * (p : ℂ)) =
      (((v * N : ℤ) : ℂ) / 24) + (((u * N : ℤ) : ℂ) / (p : ℂ)) := by
    calc
      _ = (24 * (u : ℂ) + (p : ℂ) * (v : ℂ)) * (N : ℂ) / (24 * (p : ℂ)) := by rw [hB, one_mul]
      _ = _ := by push_cast; field_simp [hPC] <;> ring
  have hPhase : Complex.exp ((Real.pi : ℂ) * Complex.I * ((dedekindSum (h : ℤ) p : ℝ) : ℂ)) =
      exponentialPhase ((N : ℂ) / (24 * (p : ℂ))) := by
    unfold exponentialPhase
    rw [hNX]
    congr 1
    field_simp [hPC] <;> ring
  have hVsplit : (((v * N₁ + v * (6 * (1 - χ)) : ℤ) : ℂ) / 24) =
      (((v * N₁ : ℤ) : ℂ) / 24) + (((v * (6 * (1 - χ)) : ℤ) : ℂ) / 24) := by
    push_cast
    ring
  have hSign := expPhase_legendre_shift hC v (inverse_two_odd hp huv)
  rw [hPhase, hSplit, expPhase_add, expPhase_div_eq_of_dvd_sub (D := p) hp0 _ _ hU]
  rw [expPhase_div_eq_of_dvd_sub (D := 24) (by decide : 0 < 24) _ _ hV, hVsplit, expPhase_add, hSign]

end
end ManuscriptAudit.Paper8DedekindPrimeSaliePhase

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8DedekindPrimeSaliePhase.dedekind_prime_salie_summand
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
