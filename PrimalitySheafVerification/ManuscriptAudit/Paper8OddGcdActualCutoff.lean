import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddGcdArithmeticRows
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddDivisorCutoff

/-! Exact cutoff identity for the odd-gcd sector of the actual lower contour Fourier coefficients. -/

namespace ManuscriptAudit.Paper8OddGcdActualCutoff

open Paper8AllResidueDivisorSum Paper8ReciprocalCommonFourier Paper8ReciprocalArithmeticRows
open Paper8ContourGammaSeries (coefficient)
open Paper8ContourResidueWeights (prefactor reducedResidues)
open Paper8OddGcdOrderedLimit (oddScale)
open Paper8OddGcdArithmeticRows Paper8OddDivisorCutoff

noncomputable section

def oddClassPart (k n : ℕ) : ℂ :=
  -prefactor k * ((coefficient k 0 : ℂ) *
    ∑ g ∈ (2*k).divisors.filter Odd, reducedFrequencySum ((2*k)/g) (shiftedFrequency k n))

private theorem odd_divisors_double {k : ℕ} (hk : 0 < k) :
    (2*k).divisors.filter Odd = k.divisors.filter Odd := by
  ext g
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hD,_⟩,hOdd⟩
    have hg₂ : ¬ 2 ∣ g := by
      intro hh
      exact (Nat.not_even_iff_odd.mpr hOdd) (even_iff_two_dvd.mpr hh)
    have hcop : Nat.Coprime g 2 := (Nat.prime_two.coprime_iff_not_dvd.mpr hg₂).symm
    exact ⟨⟨hcop.dvd_of_dvd_mul_left hD,hk.ne'⟩,hOdd⟩
  · rintro ⟨⟨hD,_⟩,hOdd⟩
    exact ⟨⟨hD.trans (dvd_mul_left k 2), by positivity⟩,hOdd⟩

theorem odd_class_row {k : ℕ} (hk : 0 < k) (n : ℕ) :
    oddClassPart k n =
      ∑ g ∈ k.divisors.filter Odd, oddScale g * fourierCoefficient reducedResidues (k/g) n := by
  unfold oddClassPart
  rw [odd_divisors_double hk]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g hg
  obtain ⟨hD,hOdd⟩ := Finset.mem_filter.mp hg
  have hg₀ : 0 < g := by
    obtain ⟨p,hp⟩ := hOdd
    omega
  obtain ⟨l,rfl⟩ := Nat.dvd_of_mem_divisors hD
  have hl : 0 < l := Nat.pos_of_ne_zero fun h => by simp [h] at hk
  have hMul : 2*(g*l) = g*(2*l) := by ac_rfl
  rw [Nat.mul_div_cancel_left l hg₀, hMul, Nat.mul_div_cancel_left (2*l) hg₀]
  exact odd_residue_class_fourier_rescale hOdd hl n

theorem finite_odd_gcd_cutoff (N n : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, oddClassPart k n) =
      ∑ g ∈ (Finset.Icc 1 N).filter Odd,
        ∑ l ∈ Finset.Icc 1 (N/g), oddScale g * fourierCoefficient reducedResidues l n := by
  calc
    _ = ∑ k ∈ Finset.Icc 1 N,
        ∑ g ∈ k.divisors.filter Odd, oddScale g * fourierCoefficient reducedResidues (k/g) n :=
      Finset.sum_congr rfl (fun _ hk => odd_class_row (Finset.mem_Icc.mp hk).1 n)
    _ = _ := commute_cutoff N (fun g l => oddScale g * fourierCoefficient reducedResidues l n)

end
end ManuscriptAudit.Paper8OddGcdActualCutoff

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8OddGcdActualCutoff.odd_class_row,
      ``ManuscriptAudit.Paper8OddGcdActualCutoff.finite_odd_gcd_cutoff] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
