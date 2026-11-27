import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddGcdActualCutoff
import PrimalitySheafVerification.ManuscriptAudit.Paper8EvenGcdOrderedLimit

/-!
# Exact odd and even sectors of the literal finite Fourier cutoff

The signed all-residue Fourier row first splits by divisor parity.
Doubling maps divisors of k to even divisors of 2k. Reordering at
a fixed finite modulus cutoff identifies the even sector with the
positive pairs h,D of product at most the cutoff.
-/

namespace ManuscriptAudit.Paper8AllResidueFiniteCutoff

open Paper8ContourGammaSeries (coefficient)
open Paper8ContourResidueWeights (prefactor reducedResidues)
open Paper8AllResidueDivisorSum (reducedFrequencySum all_frequency_sum_eq_divisor_sum)
open Paper8GcdArithmeticWeight (frequencyWeight)
open Paper8ReciprocalArithmeticRows (shiftedFrequency arithmeticSum fourierCoefficient_eq_arithmeticSum)
open Paper8ReciprocalCommonFourier (fourierCoefficient orderedFourierCoefficient)
open Paper8EvenGcdOrderedLimit (evenSectorCutoff)
open Paper8OddGcdActualCutoff (oddClassPart finite_odd_gcd_cutoff)
open Paper8OddGcdOrderedLimit (oddScale)
open Paper8OddDivisorCutoff (commute_all_cutoff)

noncomputable section

def evenClassPart (k n : ℕ) : ℂ :=
  -prefactor k * ((coefficient k 0 : ℂ) *
    ∑ g ∈ (2 * k).divisors.filter (fun g => ¬ Odd g),
      reducedFrequencySum ((2 * k) / g) (shiftedFrequency k n))

theorem all_residue_row_eq_odd_add_even {k : ℕ} (hk : 0 < k) (n : ℕ) :
    fourierCoefficient (fun _ => Finset.univ) k n = oddClassPart k n + evenClassPart k n := by
  rw [fourierCoefficient_eq_arithmeticSum (fun _ => Finset.univ) hk]
  have hAll : arithmeticSum (fun _ => Finset.univ) k (shiftedFrequency k n) =
      ∑ d : Fin (2 * k), frequencyWeight (2 * k) (shiftedFrequency k n) d := by
    unfold arithmeticSum frequencyWeight
    simp only [Nat.cast_mul, Nat.cast_ofNat]
  rw [hAll, all_frequency_sum_eq_divisor_sum (Nat.mul_pos (by decide) hk)]
  rw [← Finset.sum_filter_add_sum_filter_not (2 * k).divisors Odd
    (fun g => reducedFrequencySum ((2 * k) / g) (shiftedFrequency k n))]
  simp only [oddClassPart, evenClassPart, mul_add]

theorem even_class_row_reindex {k : ℕ} (hk : 0 < k) (n : ℕ) :
    evenClassPart k n = ∑ h ∈ k.divisors,
      -prefactor k * ((coefficient k 0 : ℂ) *
        reducedFrequencySum (k / h) (shiftedFrequency k n)) := by
  unfold evenClassPart
  simp only [Finset.mul_sum]
  symm
  refine Finset.sum_bij (fun h _ => 2 * h) ?_ ?_ ?_ ?_
  · intro h hh
    refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨?_, (Nat.mul_pos (by decide) hk).ne'⟩, ?_⟩
    · exact Nat.mul_dvd_mul_left 2 (Nat.dvd_of_mem_divisors hh)
    · exact Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr ⟨h, rfl⟩)
  · intro h _ j _ hEq
    exact mul_left_cancel₀ (by decide : (2 : ℕ) ≠ 0) hEq
  · intro g hg
    obtain ⟨hD, hEven⟩ := Finset.mem_filter.mp hg
    obtain ⟨h, rfl⟩ := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hEven)
    have hd : h ∣ k := Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < (2 : ℕ))
      (Nat.dvd_of_mem_divisors hD)
    exact ⟨h, Nat.mem_divisors.mpr ⟨hd, hk.ne'⟩, rfl⟩
  · intro h hh
    have hPos := Nat.pos_of_mem_divisors hh
    obtain ⟨D, hkMul⟩ := Nat.dvd_of_mem_divisors hh
    have hQuot : (2 * k) / (2 * h) = k / h := by
      rw [hkMul, ← mul_assoc, Nat.mul_div_cancel_left D (Nat.mul_pos (by decide) hPos),
        Nat.mul_div_cancel_left D hPos]
    rw [hQuot]

theorem sum_range_add_one_eq_Icc {A : Type*} [AddCommMonoid A]
    (N : ℕ) (f : ℕ → A) :
    (∑ i ∈ Finset.range N, f (i + 1)) = ∑ k ∈ Finset.Icc 1 N, f k := by
  refine Finset.sum_bij (fun i _ => i + 1) ?_ ?_ ?_ ?_
  · intro i hi
    have h := Finset.mem_range.mp hi
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro i _ j _ h
    omega
  · intro k hk
    obtain ⟨h₁, h₂⟩ := Finset.mem_Icc.mp hk
    exact ⟨k - 1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro i _
    rfl

theorem finite_even_gcd_cutoff (N n : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, evenClassPart k n) = evenSectorCutoff N n := by
  let f (h D : ℕ) : ℂ :=
    -prefactor (h * D) * ((coefficient (h * D) 0 : ℂ) *
      reducedFrequencySum D (shiftedFrequency (h * D) n))
  calc
    _ = ∑ k ∈ Finset.Icc 1 N, ∑ h ∈ k.divisors, f h (k / h) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [even_class_row_reindex (Finset.mem_Icc.mp hk).1 n]
      refine Finset.sum_congr rfl fun h hh => ?_
      unfold f
      rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hh)]
    _ = ∑ h ∈ Finset.Icc 1 N, ∑ D ∈ Finset.Icc 1 (N / h), f h D :=
      commute_all_cutoff N f
    _ = _ := by
      change (∑ h ∈ Finset.Icc 1 N, ∑ D ∈ Finset.Icc 1 (N / h), f h D) =
        ∑ h ∈ Finset.range N, ∑ d ∈ Finset.range (N / (h + 1)), f (h + 1) (d + 1)
      rw [← sum_range_add_one_eq_Icc N (fun h => ∑ D ∈ Finset.Icc 1 (N / h), f h D)]
      exact Finset.sum_congr rfl (fun h _ => (sum_range_add_one_eq_Icc (N / (h + 1)) (f (h + 1))).symm)

theorem finite_all_residue_fourier_cutoff (N n : ℕ) :
    orderedFourierCoefficient (fun _ => Finset.univ) N n =
      (∑ g ∈ (Finset.Icc 1 N).filter Odd,
        ∑ D ∈ Finset.Icc 1 (N / g), oddScale g * fourierCoefficient reducedResidues D n) +
      evenSectorCutoff N n := by
  unfold orderedFourierCoefficient
  rw [sum_range_add_one_eq_Icc N (fun k => fourierCoefficient (fun _ => Finset.univ) k n),
    ← finite_odd_gcd_cutoff N n, ← finite_even_gcd_cutoff N n, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl
    (fun k hk => all_residue_row_eq_odd_add_even (Finset.mem_Icc.mp hk).1 n)

end
end ManuscriptAudit.Paper8AllResidueFiniteCutoff

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8AllResidueFiniteCutoff.all_residue_row_eq_odd_add_even,
      ``ManuscriptAudit.Paper8AllResidueFiniteCutoff.even_class_row_reindex,
      ``ManuscriptAudit.Paper8AllResidueFiniteCutoff.finite_even_gcd_cutoff,
      ``ManuscriptAudit.Paper8AllResidueFiniteCutoff.finite_all_residue_fourier_cutoff] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
