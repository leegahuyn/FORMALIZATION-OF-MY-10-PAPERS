import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import PrimalitySheafVerification.ManuscriptAudit.Paper5AnalyticEuler
import PrimalitySheafVerification.ManuscriptAudit.LocalTraceExponential

/-! The actual extension point counts give the analytic local zeta for every good centered cubic. -/

namespace ManuscriptAudit.Paper5ActualAnalyticLocalZeta

open PowerSeries Paper5ActualHasseWeil Paper5AnalyticEuler
open PointCountExponential LocalTraceExponential

noncomputable section

def pointTerm (p : ℕ) [Fact p.Prime] (A : ZMod p) (z : ℂ) (n : ℕ) : ℂ :=
  PowerSeries.coeff (n+1) (actualCounts p A) * z^(n+1) / ((n+1 : ℕ) : ℂ)

theorem actual_local_zeta (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    {A : ZMod p} (hA : A ≠ 0) {z : ℂ} (hz : ‖z‖ < 1 / (p : ℝ)) :
    Summable (fun n : ℕ => ‖pointTerm p A z n‖) ∧
      Complex.exp (∑' n : ℕ, pointTerm p A z n) =
        (1 - (firstTrace p A : ℂ) * z + (p : ℂ) * z^2) /
          ((1-z) * (1-(p : ℂ)*z)) := by
  obtain ⟨α, β, ha, hm, hα, hβ⟩ := exists_actual_roots hp hA
  have hpR : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp₁ : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  have hpz : (p : ℝ) * ‖z‖ < 1 := by
    rw [mul_comm]
    exact (lt_div_iff₀ hpR).mp hz
  have hz₁ : ‖z‖ < 1 := (le_mul_of_one_le_left (norm_nonneg z) hp₁).trans_lt hpz
  have hpCz : ‖(p : ℂ) * z‖ < 1 := by
    simpa only [norm_mul, Complex.norm_natCast] using hpz
  have hS : Real.sqrt p ≤ p := (Real.sqrt_le_self_iff).mpr (Or.inr hp₁)
  have hαz : ‖α * z‖ < 1 := by
    rw [norm_mul, hα]
    exact (mul_le_mul_of_nonneg_right hS (norm_nonneg _)).trans_lt hpz
  have hβz : ‖β * z‖ < 1 := by
    rw [norm_mul, hβ]
    exact (mul_le_mul_of_nonneg_right hS (norm_nonneg _)).trans_lt hpz
  have hTerm (n : ℕ) : pointTerm p A z n =
      term n ((p : ℂ)*z) + term n z - term n (α*z) - term n (β*z) := by
    unfold pointTerm
    rw [actualCounts_eq p hp hA α β ha hm]
    simp only [twoRootCounts, coeff_succ_X_mul, coeff_mk, term, mul_pow]
    ring
  have hAbs := (((term_norm_summable hpCz).add (term_norm_summable hz₁)).add
    (term_norm_summable hαz)).add (term_norm_summable hβz)
  have hSum : HasSum (pointTerm p A z)
      (traceLog ((p : ℂ)*z) + traceLog z - traceLog (α*z) - traceLog (β*z)) := by
    have h := (((traceLog_hasSum hpCz).add (traceLog_hasSum hz₁)).sub
      (traceLog_hasSum hαz)).sub (traceLog_hasSum hβz)
    have he : (fun n : ℕ => term n ((p : ℂ)*z) + term n z -
        term n (α*z) - term n (β*z)) = pointTerm p A z :=
      funext (fun n => (hTerm n).symm)
    rw [he] at h
    exact h
  constructor
  · apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hAbs
    intro n
    rw [hTerm]
    calc
      _ ≤ ‖term n ((p : ℂ)*z) + term n z - term n (α*z)‖ + ‖term n (β*z)‖ :=
        norm_sub_le _ _
      _ ≤ (‖term n ((p : ℂ)*z) + term n z‖ + ‖term n (α*z)‖) + ‖term n (β*z)‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ _ := add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl
  · rw [hSum.tsum_eq, Complex.exp_sub, Complex.exp_sub, Complex.exp_add,
      exp_traceLog hpCz, exp_traceLog hz₁, exp_traceLog hαz, exp_traceLog hβz]
    have hFactor : (1-α*z)*(1-β*z) = 1 - (firstTrace p A : ℂ)*z + (p : ℂ)*z^2 := by
      linear_combination -z*ha + z^2*hm
    rw [← hFactor]
    have hNZ (w : ℂ) (hw : ‖w‖ < 1) : (1 : ℂ) - w ≠ 0 := by
      intro h
      have he : (1 : ℂ) = w := sub_eq_zero.mp h
      simpa only [← he, norm_one, lt_irrefl] using hw
    field_simp [hNZ _ hpCz, hNZ _ hz₁, hNZ _ hαz, hNZ _ hβz] <;> ring

def rationalZeta (q a z : ℂ) : ℂ :=
  (1-a*z+q*z^2)/((1-z)*(1-q*z))

/-- The finite-valued rational continuation has the genus-one reciprocal symmetry. -/
theorem rational_zeta_inversion {q a z : ℂ} (hq : q ≠ 0) (hz : z ≠ 0)
    (h₁ : 1-z ≠ 0) (h₂ : 1-q*z ≠ 0) :
    rationalZeta q a (q*z)⁻¹ = rationalZeta q a z := by
  have hInv₁ : 1-(q*z)⁻¹ = -(1-q*z)*(q*z)⁻¹ := by
    field_simp [hq,hz] <;> ring
  have hInv₂ : 1-q*(q*z)⁻¹ = -(1-z)*z⁻¹ := by
    field_simp [hq,hz] <;> ring
  unfold rationalZeta
  rw [hInv₁, hInv₂]
  field_simp [hq,hz,h₁,h₂] <;> ring

end
end ManuscriptAudit.Paper5ActualAnalyticLocalZeta

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.Paper5ActualAnalyticLocalZeta.actual_local_zeta,
      ``ManuscriptAudit.Paper5ActualAnalyticLocalZeta.rational_zeta_inversion] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
