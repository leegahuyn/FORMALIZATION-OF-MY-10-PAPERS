import Lean.Util.CollectAxioms
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import PrimalitySheafVerification.ManuscriptAudit.Paper8DedekindPrimeSaliePhase
import PrimalitySheafVerification.ManuscriptAudit.Paper8PrimeSalieBound
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossCuspCutoff

/-! The manuscript's genuine odd arithmetic sum has the square-root bound at every prime p ≥ 5. -/

namespace ManuscriptAudit.Paper8OddCrossPrimeBound

open Finset Paper8ContourResidueWeights Paper8DedekindZeroReference Paper8OddCrossCuspPhase
open Paper8DedekindKloostermanCongruence Paper8DedekindPrimeSaliePhase
open Paper8PrimeQuadraticPhase Paper8PrimeSalieBound Paper8OddCrossPoincareKernel
open Paper8OddCrossCuspCutoff Paper8OddCrossCuspRows

noncomputable section

private theorem stdAddChar_eq_phase {p : ℕ} [NeZero p] (m : ℤ) :
    ZMod.stdAddChar (m : ZMod p) = exponentialPhase ((m : ℂ) / (p : ℂ)) := by
  rw [ZMod.stdAddChar_coe, exponentialPhase]
  congr 1
  ring

private theorem finEquiv_apply_cast {p : ℕ} [NeZero p] (d : Fin p) :
    ZMod.finEquiv p d = (d.val : ZMod p) := by
  have hVal : (ZMod.finEquiv p d).val = d.val := by
    cases p with
    | zero => exact Fin.elim0 d
    | succ p => rfl
  have h := ZMod.natCast_zmod_val (ZMod.finEquiv p d)
  rw [hVal] at h
  exact h.symm

private theorem choose_odd_representative {p d : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    ∃ h : ℕ, h % 2 = 1 ∧ (h : ZMod p) = (d : ZMod p) ∧
      dedekindSum (h : ℤ) p = dedekindSum (d : ℤ) p := by
  have hp2 := (Nat.Prime.mod_two_eq_one_iff_ne_two (Fact.out : p.Prime)).2 hp
  by_cases hd : d % 2 = 1
  · exact ⟨d, hd, rfl, rfl⟩
  · refine ⟨d + p, by omega, ?_, ?_⟩
    · rw [Nat.cast_add, ZMod.natCast_self, add_zero]
    · have h := dedekind_translate (Fact.out : p.Prime).pos (d : ℤ) 1
      simpa only [Nat.cast_add, mul_one] using h

private theorem coprime_of_cast_ne_zero {p h : ℕ} [Fact p.Prime] (hn : (h : ZMod p) ≠ 0) :
    h.Coprime p :=
  ((Fact.out : p.Prime).coprime_iff_not_dvd.2
    ((not_congr (ZMod.natCast_eq_zero_iff h p)).1 hn)).symm

private theorem reference_entry_prime {p d : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hp3 : ¬ (3 : ℕ) ∣ p) (hd : d.Coprime p) {u v : ℤ} (huv : 24 * u + (p : ℤ) * v = 1) :
    Complex.exp ((Real.pi : ℂ) * Complex.I * ((dedekindSum (d : ℤ) p : ℝ) : ℂ)) =
      exponentialPhase (((v * dedekindPhaseNumerator 1 p : ℤ) : ℂ) / 24) *
        (primeQuadraticChar p (d : ZMod p) *
          ZMod.stdAddChar ((u : ZMod p) * (d : ZMod p) + (u : ZMod p) / (d : ZMod p))) := by
  obtain ⟨h, hh, hCast, hDed⟩ := choose_odd_representative (d := d) hp
  have hD : (d : ZMod p) ≠ 0 := (ZMod.unitOfCoprime d hd).ne_zero
  have hC : h.Coprime p := coprime_of_cast_ne_zero (hCast.symm ▸ hD)
  let a : ℤ := ((d : ZMod p)⁻¹).val
  have ha : (a : ZMod p) = (d : ZMod p)⁻¹ := by
    dsimp only [a]
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hInv : (h : ZMod p) * (a : ZMod p) = 1 := by
    rw [hCast, ha, mul_inv_cancel₀ hD]
  have hTerm := dedekind_prime_salie_summand hp hp3 hh hC u v a huv hInv
  rw [hDed] at hTerm
  have hChar : (legendreSym p (h : ℤ) : ℂ) = primeQuadraticChar p (d : ZMod p) := by
    rw [legendreSym, Int.cast_natCast, hCast] <;> rfl
  have hPhase :
      exponentialPhase (((u * ((h : ℤ) + a) : ℤ) : ℂ) / (p : ℂ)) =
        ZMod.stdAddChar ((u : ZMod p) * (d : ZMod p) + (u : ZMod p) / (d : ZMod p)) := by
    rw [← stdAddChar_eq_phase]
    congr 1
    push_cast
    rw [hCast, ha, mul_add, div_eq_mul_inv]
  rw [hChar, hPhase, mul_assoc] at hTerm
  exact hTerm

private theorem referenceZeroSum_eq_primeSalie {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hp3 : ¬ (3 : ℕ) ∣ p) {u v : ℤ} (huv : 24 * u + (p : ℤ) * v = 1) :
    referenceZeroSum p =
      exponentialPhase (((v * dedekindPhaseNumerator 1 p : ℤ) : ℂ) / 24) *
        primeSalieSum ZMod.stdAddChar (u : ZMod p) (u : ZMod p) := by
  unfold referenceZeroSum primeSalieSum
  rw [Finset.sum_filter, Finset.mul_sum]
  apply Fintype.sum_equiv (ZMod.finEquiv p).toEquiv _ _
  intro d
  rw [show (ZMod.finEquiv p).toEquiv d = (d.val : ZMod p) from finEquiv_apply_cast d]
  by_cases hd : d.val.Coprime p
  · rw [if_pos hd]
    exact reference_entry_prime hp hp3 hd huv
  · have hZero : (d.val : ZMod p) = 0 :=
      not_ne_iff.mp (fun h => hd (coprime_of_cast_ne_zero h))
    simp [if_neg hd, hZero, primeQuadraticChar_apply]

private theorem coprime_twentyFour_of_prime_ge_five {p : ℕ} [Fact p.Prime] (hP : 5 ≤ p) :
    (24 : ℕ).Coprime p := by
  have hPrime := (Fact.out : p.Prime)
  have h2 : ¬ p ∣ 2 := fun h => by
    have hp := Nat.le_of_dvd (by decide : 0 < 2) h
    omega
  have h3 : ¬ p ∣ 3 := fun h => by
    have hp := Nat.le_of_dvd (by decide : 0 < 3) h
    omega
  apply (hPrime.coprime_iff_not_dvd.2 ?_).symm
  rw [show (24 : ℕ) = 3 * (2 * (2 * 2)) by norm_num]
  simp [hPrime.dvd_mul, h2, h3]

private theorem norm_referenceZeroSum_prime {p : ℕ} [Fact p.Prime] (hP : 5 ≤ p) :
    ‖referenceZeroSum p‖ ≤ 2 * Real.sqrt (p : ℝ) := by
  let u := Nat.gcdA 24 p
  let v := Nat.gcdB 24 p
  have hC := coprime_twentyFour_of_prime_ge_five hP
  have huv : 24 * u + (p : ℤ) * v = 1 := by
    have h := Nat.gcd_eq_gcd_ab 24 p
    change (Nat.gcd 24 p : ℤ) = 24 * u + (p : ℤ) * v at h
    have hg : Nat.gcd 24 p = 1 := hC
    rw [hg, Nat.cast_one] at h
    exact h.symm
  have hp : p ≠ 2 := by omega
  have hp3 : ¬ (3 : ℕ) ∣ p := fun h => by
    have hp' := ((Fact.out : p.Prime).dvd_iff_eq (by decide : (3 : ℕ) ≠ 1)).1 h
    omega
  have hu : (u : ZMod p) ≠ 0 := by
    intro h0
    have h := congrArg (fun z : ℤ => (z : ZMod p)) huv
    push_cast at h
    simp [h0] at h
  have hNorm : ‖exponentialPhase (((v * dedekindPhaseNumerator 1 p : ℤ) : ℂ) / 24)‖ = 1 := by
    unfold exponentialPhase
    rw [Complex.norm_exp]
    push_cast
    norm_num [Complex.mul_re, Complex.mul_im, Complex.div_ofNat_re, Complex.div_ofNat_im]
  rw [referenceZeroSum_eq_primeSalie hp hp3 huv, norm_mul, hNorm, one_mul]
  exact norm_primeSalieSum_le hp (ZMod.isPrimitive_stdAddChar p) (u : ZMod p) hu

theorem norm_oddCrossSum_prime {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) :
    ‖crossSum (Fact.out : p.Prime).pos‖ ≤ 2 * Real.sqrt (p : ℝ) := by
  rw [crossSum_eq (Fact.out : p.Prime).pos, norm_mul]
  have hC : ‖(chiFour (p : ZMod 4) : ℂ)‖ ≤ 1 := by
    unfold chiFour
    split_ifs <;> norm_num
  exact (mul_le_of_le_one_left (norm_nonneg _) hC).trans (norm_referenceZeroSum_prime hp)

end
end ManuscriptAudit.Paper8OddCrossPrimeBound

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8OddCrossPrimeBound.norm_oddCrossSum_prime
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
