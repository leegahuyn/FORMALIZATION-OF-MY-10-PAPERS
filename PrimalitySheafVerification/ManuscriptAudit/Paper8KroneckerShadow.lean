import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8HolomorphicPartPhase

/-!
# The exact unary target series on physical pp. 332 and 338

In the root coordinate `w=exp(2πiτ/24)` the series consists of the
terms `χ(n) n w^(n²)`. Index zero contributes zero. The estimates prove
absolute convergence and holomorphy on the actual upper half-plane.
-/

namespace ManuscriptAudit.Paper8KroneckerShadow

open Paper8ExteriorNormalization (kroneckerNegTwelve)
open Paper8HolomorphicPartPhase (periodCoefficient qParameter qParameter_norm_lt_one)

noncomputable section

def coefficient (n : ℕ) : ℂ := (kroneckerNegTwelve (n : ℤ) : ℂ) * (n : ℂ)

def shadowTerm (n : ℕ) (w : ℂ) : ℂ := coefficient n * w ^ (n ^ 2)

def shadowSeries (w : ℂ) : ℂ := ∑' n : ℕ, shadowTerm n w

def rootParameter (τ : ℂ) : ℂ := Complex.exp ((periodCoefficient / 24) * τ)

def unaryShadow (τ : ℂ) : ℂ := shadowSeries (rootParameter τ)

private theorem norm_kronecker_le_one (m : ℤ) :
    ‖(kroneckerNegTwelve m : ℂ)‖ ≤ 1 := by
  rcases jacobiSym.trichotomy (-12) m.natAbs with h | h | h <;>
    unfold kroneckerNegTwelve <;> split_ifs <;> simp [h]

theorem norm_coefficient_le (n : ℕ) : ‖coefficient n‖ ≤ (n : ℝ) := by
  have hNat : ‖(n : ℂ)‖ = (n : ℝ) := by
    rw [← Complex.ofReal_natCast, Complex.norm_real, Real.norm_of_nonneg (Nat.cast_nonneg n)]
  rw [coefficient, norm_mul, hNat]
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right (norm_kronecker_le_one (n : ℤ)) (Nat.cast_nonneg n)

private theorem le_square (n : ℕ) : n ≤ n ^ 2 := by
  cases n with
  | zero => decide
  | succ n =>
      simpa only [pow_two, mul_one] using Nat.mul_le_mul_left (n + 1) (by omega : 1 ≤ n + 1)

theorem term_bound {w : ℂ} {r : ℝ} (hwr : ‖w‖ ≤ r) (h₁ : r < 1) (n : ℕ) :
    ‖shadowTerm n w‖ ≤ (n : ℝ) * r ^ n := by
  have hr : 0 ≤ r := (norm_nonneg w).trans hwr
  have hPow : ‖w‖ ^ (n ^ 2) ≤ r ^ n :=
    (pow_le_pow_left₀ (norm_nonneg w) hwr _).trans
      (pow_le_pow_of_le_one hr h₁.le (le_square n))
  rw [shadowTerm, norm_mul, norm_pow]
  exact mul_le_mul (norm_coefficient_le n) hPow (pow_nonneg (norm_nonneg w) _) (Nat.cast_nonneg n)

private theorem majorant_summable {r : ℝ} (hr : 0 ≤ r) (h₁ : r < 1) :
    Summable (fun n : ℕ => (n : ℝ) * r ^ n) := by
  simpa only [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1
    (r := r) (by simpa only [Real.norm_of_nonneg hr] using h₁)

theorem shadowSeries_absolute_summability {w : ℂ} (hw : ‖w‖ < 1) :
    Summable (fun n => ‖shadowTerm n w‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => term_bound le_rfl hw n)
    (majorant_summable (norm_nonneg w) hw)

theorem shadowSeries_differentiableOn_unit_disk :
    DifferentiableOn ℂ shadowSeries (Metric.ball (0 : ℂ) 1) := by
  intro w hw
  have hw₁ : ‖w‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hw
  let r : ℝ := (‖w‖ + 1) / 2
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hr₁ : r < 1 := by dsimp [r]; linarith
  have hwr : w ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right]
    dsimp [r]
    linarith
  have hTerm (n : ℕ) : DifferentiableOn ℂ (shadowTerm n) (Metric.ball (0 : ℂ) r) :=
    ((differentiable_const (c := coefficient n)).mul (differentiable_id.pow (n ^ 2))).differentiableOn
  have h := Complex.differentiableOn_tsum_of_summable_norm (F := shadowTerm)
    (majorant_summable hr hr₁) hTerm Metric.isOpen_ball (fun n z hz =>
      term_bound (by simpa only [dist_zero_right] using (Metric.mem_ball.mp hz).le) hr₁ n)
  exact ((h w hwr).differentiableAt (Metric.isOpen_ball.mem_nhds hwr)).differentiableWithinAt

theorem rootParameter_pow (τ : ℂ) : rootParameter τ ^ (24 : ℕ) = qParameter τ := by
  rw [rootParameter, qParameter, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem rootParameter_norm_lt_one {τ : ℂ} (hτ : 0 < τ.im) : ‖rootParameter τ‖ < 1 := by
  by_contra! h
  have hLe := pow_le_pow_left₀ (zero_le_one : (0 : ℝ) ≤ 1) h (24 : ℕ)
  rw [← norm_pow, rootParameter_pow, one_pow] at hLe
  exact (not_le_of_gt (qParameter_norm_lt_one hτ)) hLe

theorem shadowTerm_root_eq_exponential (n : ℕ) (τ : ℂ) :
    shadowTerm n (rootParameter τ) =
      coefficient n * Complex.exp (periodCoefficient * (n : ℂ) ^ 2 * τ / 24) := by
  rw [shadowTerm, rootParameter, ← Complex.exp_nat_mul]
  congr 2 <;> push_cast <;> ring

theorem unaryShadow_absolute_summability {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun n => ‖coefficient n * Complex.exp (periodCoefficient * (n : ℂ) ^ 2 * τ / 24)‖) := by
  simpa only [shadowTerm_root_eq_exponential] using
    shadowSeries_absolute_summability (rootParameter_norm_lt_one hτ)

theorem unaryShadow_differentiableOn :
    DifferentiableOn ℂ unaryShadow {τ : ℂ | 0 < τ.im} := by
  have hRoot : Differentiable ℂ rootParameter :=
    Complex.differentiable_exp.comp
      ((differentiable_const (c := periodCoefficient / 24)).mul differentiable_id)
  have hMaps : Set.MapsTo rootParameter {τ : ℂ | 0 < τ.im} (Metric.ball (0 : ℂ) 1) :=
    fun τ hτ => by
      simpa only [Metric.mem_ball, dist_zero_right] using rootParameter_norm_lt_one hτ
  exact shadowSeries_differentiableOn_unit_disk.comp hRoot.differentiableOn hMaps

end
end ManuscriptAudit.Paper8KroneckerShadow

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8KroneckerShadow.norm_coefficient_le,
      ``ManuscriptAudit.Paper8KroneckerShadow.shadowSeries_absolute_summability,
      ``ManuscriptAudit.Paper8KroneckerShadow.shadowSeries_differentiableOn_unit_disk,
      ``ManuscriptAudit.Paper8KroneckerShadow.rootParameter_pow,
      ``ManuscriptAudit.Paper8KroneckerShadow.shadowTerm_root_eq_exponential,
      ``ManuscriptAudit.Paper8KroneckerShadow.unaryShadow_absolute_summability,
      ``ManuscriptAudit.Paper8KroneckerShadow.unaryShadow_differentiableOn] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
