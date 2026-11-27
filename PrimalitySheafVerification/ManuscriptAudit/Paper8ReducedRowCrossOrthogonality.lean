import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8ShiftedRowOrthogonality

/-!
# Cross-modulus orthogonality of the shifted reduced rows

The reduced numerators have primitive phase order 2k. Distinct
moduli therefore have disjoint residue frequencies. Averaging over
a common finite period makes the correlation vanish exactly.
-/

namespace ManuscriptAudit.Paper8ReducedRowCrossOrthogonality

open Paper8ContourResidueWeights (reducedResidues)
open Paper8ContourDifferenceTerms (root_power_norm)
open Paper8ReciprocalCommonFourier (fourierCoefficient)
open Paper8ShiftedRowOrthogonality (root_is_primitive rootFrequency shiftedInput
  fourierCoefficient_eq_sum_inputs geom_sum_eq)

noncomputable section

theorem reduced_phase_primitive {k : ℕ} (hk : 0 < k) {d : Fin (2 * k)}
    (hd : d ∈ reducedResidues k) : IsPrimitiveRoot (rootFrequency k d) (2 * k) := by
  have hC : Nat.Coprime d.val (2 * k) := (Finset.mem_filter.mp hd).2
  rw [rootFrequency, zpow_natCast]
  exact ((root_is_primitive hk).pow_of_coprime d.val hC).inv

private theorem conj_phase_mul_phase (k : ℕ) (d : Fin (2 * k)) :
    (starRingEnd ℂ) (rootFrequency k d) * rootFrequency k d = 1 := by
  have hNorm : ‖rootFrequency k d‖ = 1 := by
    rw [rootFrequency, norm_inv, root_power_norm, inv_one]
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hNorm]
  norm_num

theorem reduced_cross_phase_sum {k ℓ M : ℕ} (hk : 0 < k) (hℓ : 0 < ℓ) (h : k ≠ ℓ)
    (hkM : 2 * k ∣ M) (hℓM : 2 * ℓ ∣ M) {d : Fin (2 * k)} {e : Fin (2 * ℓ)}
    (hd : d ∈ reducedResidues k) (he : e ∈ reducedResidues ℓ) :
    (∑ n ∈ Finset.range M,
      (rootFrequency k d * (starRingEnd ℂ) (rootFrequency ℓ e)) ^ n) = 0 := by
  have hkd := reduced_phase_primitive hk hd
  have hℓe := reduced_phase_primitive hℓ he
  let u : ℂ := rootFrequency k d * (starRingEnd ℂ) (rootFrequency ℓ e)
  have hPow : u ^ M = 1 := by
    unfold u
    rw [mul_pow, (hkd.pow_eq_one_iff_dvd M).2 hkM, ← map_pow,
      (hℓe.pow_eq_one_iff_dvd M).2 hℓM, map_one, one_mul]
  have hU : u ≠ 1 := by
    intro hu
    have hp : rootFrequency k d = rootFrequency ℓ e := by
      calc
        _ = rootFrequency k d *
            ((starRingEnd ℂ) (rootFrequency ℓ e) * rootFrequency ℓ e) := by
          rw [conj_phase_mul_phase, mul_one]
        _ = _ := by
          rw [← mul_assoc]
          change u * rootFrequency ℓ e = _
          rw [hu, one_mul]
    have hOther : IsPrimitiveRoot (rootFrequency k d) (2 * ℓ) := by simpa only [hp] using hℓe
    have hMod := hkd.unique hOther
    exact h (by omega)
  change (∑ n ∈ Finset.range M, u ^ n) = 0
  rw [geom_sum_eq hPow, if_neg hU]

theorem reduced_cross_row_period_sum {k ℓ M : ℕ} (hk : 0 < k) (hℓ : 0 < ℓ)
    (h : k ≠ ℓ) (hkM : 2 * k ∣ M) (hℓM : 2 * ℓ ∣ M) :
    (∑ n ∈ Finset.range M, fourierCoefficient reducedResidues k n *
      (starRingEnd ℂ) (fourierCoefficient reducedResidues ℓ n)) = 0 := by
  have hExpand (n : ℕ) : fourierCoefficient reducedResidues k n *
      (starRingEnd ℂ) (fourierCoefficient reducedResidues ℓ n) =
      ∑ d ∈ reducedResidues k, ∑ e ∈ reducedResidues ℓ,
        (shiftedInput k d * (starRingEnd ℂ) (shiftedInput ℓ e)) *
          (rootFrequency k d * (starRingEnd ℂ) (rootFrequency ℓ e)) ^ n := by
    simp only [fourierCoefficient_eq_sum_inputs, map_sum, map_mul, map_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [mul_pow]
    ring
  simp only [hExpand]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun d hd => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun e he => ?_
  rw [← Finset.mul_sum, reduced_cross_phase_sum hk hℓ h hkM hℓM hd he, mul_zero]

end
end ManuscriptAudit.Paper8ReducedRowCrossOrthogonality

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ReducedRowCrossOrthogonality.reduced_phase_primitive,
      ``ManuscriptAudit.Paper8ReducedRowCrossOrthogonality.reduced_cross_phase_sum,
      ``ManuscriptAudit.Paper8ReducedRowCrossOrthogonality.reduced_cross_row_period_sum] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
