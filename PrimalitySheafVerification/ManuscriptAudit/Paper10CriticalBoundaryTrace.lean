import Lean.Util.CollectAxioms
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Failure of a point trace from the critical fractional Fourier norm

The cosine polynomials are smooth. Their endpoint value is one while
their squared critical Fourier norm can be arbitrarily small. This
tests the regularity level of the trace hypothesis on physical p. 477.
-/

namespace ManuscriptAudit.Paper10CriticalBoundaryTrace

open Filter
open scoped BigOperators Topology

noncomputable section

def frequency {n : ℕ} (j : Fin n) : ℝ := (j.val : ℝ) + 1

def harmonic (n : ℕ) : ℝ := ∑ j : Fin n, 1 / frequency j

def coefficients (n : ℕ) (j : Fin n) : ℝ := (harmonic n)⁻¹ * (1 / frequency j)

def cosinePolynomial {n : ℕ} (a : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ j, a j * Real.cos (frequency j * x)

/-- Squared Fourier norm with Sobolev exponent one half in cosine coordinates. -/
def criticalEnergy {n : ℕ} (a : Fin n → ℝ) : ℝ :=
  ∑ j, Real.sqrt (1 + frequency j ^ 2) * (a j)^2

theorem harmonic_tends_to_infinity : Tendsto harmonic atTop atTop := by
  have he : harmonic = fun n : ℕ => ∑ i ∈ Finset.range n, 1 / ((i : ℝ)+1) := by
    funext n
    unfold harmonic frequency
    rw [Fin.sum_univ_eq_sum_range]
  rw [he]
  exact Real.tendsto_sum_range_one_div_nat_succ_atTop

theorem normalized_value (n : ℕ) (hn : 0 < harmonic n) :
    cosinePolynomial (coefficients n) 0 = 1 := by
  unfold cosinePolynomial coefficients
  simp only [mul_zero, Real.cos_zero, mul_one, ← Finset.mul_sum]
  change (harmonic n)⁻¹ * harmonic n = 1
  exact inv_mul_cancel₀ hn.ne'

theorem normalized_energy_le (n : ℕ) (hn : 0 < harmonic n) :
    criticalEnergy (coefficients n) ≤ 2 / harmonic n := by
  unfold criticalEnergy
  calc
    _ ≤ ∑ j : Fin n, (2 * (1 / frequency j)) * (harmonic n)⁻¹^2 := by
      apply Finset.sum_le_sum
      intro j _
      let k := frequency j
      have hk : 1 ≤ k := by dsimp [k, frequency]; positivity
      have hk0 : 0 < k := zero_lt_one.trans_le hk
      have hquad : 1 + k^2 ≤ (2*k)^2 := by nlinarith [sq_nonneg (k-1)]
      have hs : Real.sqrt (1+k^2) ≤ 2*k := by
        have ht := Real.sqrt_le_sqrt hquad
        rw [Real.sqrt_sq (mul_nonneg (by norm_num) hk0.le)] at ht
        exact ht
      change Real.sqrt (1+k^2) * ((harmonic n)⁻¹ * (1/k))^2 ≤
        (2*(1/k))*(harmonic n)⁻¹^2
      calc
        _ ≤ (2*k) * ((harmonic n)⁻¹ * (1/k))^2 :=
          mul_le_mul_of_nonneg_right hs (sq_nonneg _)
        _ = _ := by field_simp [hk0.ne'] <;> ring
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      change (2 * harmonic n) * (harmonic n)⁻¹^2 = 2 / harmonic n
      field_simp [hn.ne'] <;> ring

theorem no_uniform_critical_endpoint_trace :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (a : Fin n → ℝ),
      |cosinePolynomial a 0|^2 ≤ C * criticalEnergy a := by
  rintro ⟨C, hC, hBound⟩
  have hLarge : ∀ᶠ n in atTop, 2*C < harmonic n := by
    filter_upwards [(tendsto_atTop.1 harmonic_tends_to_infinity) (2*C + 1)] with n hn
    linarith
  obtain ⟨n, hn⟩ := hLarge.exists
  have hn0 : 0 < harmonic n := by linarith
  have hOne := hBound n (coefficients n)
  rw [normalized_value n hn0, abs_one, one_pow] at hOne
  have hEstimate := mul_le_mul_of_nonneg_left (normalized_energy_le n hn0) hC
  have hSmall : C * (2 / harmonic n) < 1 := by
    rw [← mul_div_assoc, mul_comm C 2]
    apply (div_lt_iff₀ hn0).2
    simpa only [one_mul] using hn
  exact (hOne.trans hEstimate).not_gt hSmall

end
end ManuscriptAudit.Paper10CriticalBoundaryTrace

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper10CriticalBoundaryTrace.harmonic_tends_to_infinity,
      ``ManuscriptAudit.Paper10CriticalBoundaryTrace.normalized_value,
      ``ManuscriptAudit.Paper10CriticalBoundaryTrace.normalized_energy_le,
      ``ManuscriptAudit.Paper10CriticalBoundaryTrace.no_uniform_critical_endpoint_trace] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
