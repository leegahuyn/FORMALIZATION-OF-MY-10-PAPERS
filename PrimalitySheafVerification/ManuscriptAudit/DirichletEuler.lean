import Lean.Util.CollectAxioms
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Prime-dependent analytic Euler factors

Paper 7, physical p. 280, also proposes an analytic substitution
`T = p⁻ˢ`. With a uniform Frobenius exponent bound, the weighted
Dirichlet terms and the actual local logarithmic derivatives are
absolutely summable in the claimed open half-plane. The local
derivative is taken with respect to s and includes the factor log p.
-/

namespace ManuscriptAudit.DirichletEuler

open Nat
open scoped BigOperators

noncomputable section

def scaledRoot (p : Primes) (α s : ℂ) : ℂ := α * (p : ℂ) ^ (-s)

def localLogDerivative (p : Primes) (α s : ℂ) : ℂ :=
  -(Complex.log (p : ℂ) * scaledRoot p α s / (1 - scaledRoot p α s))

private theorem scaledRoot_norm_le (p : Primes) {α s : ℂ} {W : ℝ}
    (hα : ‖α‖ ≤ (p : ℝ) ^ W) :
    ‖scaledRoot p α s‖ ≤ (p : ℝ) ^ (W - s.re) := by
  have hp : (0 : ℝ) < p := Nat.cast_pos.mpr p.prop.pos
  rw [scaledRoot, norm_mul, Complex.norm_natCast_cpow_of_pos p.prop.pos, Complex.neg_re]
  calc
    _ ≤ (p : ℝ) ^ W * (p : ℝ) ^ (-s.re) :=
      mul_le_mul_of_nonneg_right hα (Real.rpow_nonneg hp.le _)
    _ = _ := by rw [← Real.rpow_add hp, sub_eq_add_neg]

theorem paper7_dirichlet_scaled_roots_abs_summable
    (α : Primes → ℂ) {s : ℂ} {W : ℝ} (hs : W + 1 < s.re)
    (hα : ∀ p, ‖α p‖ ≤ (p : ℝ) ^ W) :
    Summable (fun p : Primes => ‖scaledRoot p (α p) s‖) := by
  have he : W - s.re < -1 := by linarith
  have hS := (Real.summable_nat_rpow.mpr he).subtype Nat.Prime
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun p => scaledRoot_norm_le p (hα p)) hS

theorem paper7_dirichlet_local_logs_summable
    (α : Primes → ℂ) {s : ℂ} {W : ℝ} (hs : W + 1 < s.re)
    (hα : ∀ p, ‖α p‖ ≤ (p : ℝ) ^ W) :
    Summable (fun p : Primes => -Complex.log (1 - scaledRoot p (α p) s)) := by
  exact (Summable.of_norm (paper7_dirichlet_scaled_roots_abs_summable α hs hα)).clog_one_sub.neg

theorem paper7_dirichlet_local_log_hasDeriv
    (p : Primes) {α s : ℂ} {W : ℝ} (hs : W + 1 < s.re)
    (hα : ‖α‖ ≤ (p : ℝ) ^ W) :
    HasDerivAt (fun z : ℂ => -Complex.log (1 - scaledRoot p α z))
      (localLogDerivative p α s) s := by
  have hp : (1 : ℝ) < p := by exact_mod_cast p.prop.one_lt
  have hNorm := (scaledRoot_norm_le p hα).trans_lt
    (Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith : W - s.re < 0))
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr p.prop.ne_zero
  have hF : HasDerivAt (fun z : ℂ => scaledRoot p α z)
      (-(Complex.log (p : ℂ) * scaledRoot p α s)) s := by
    have h := ((hasDerivAt_neg' s).const_cpow (c := (p : ℂ)) (Or.inl hpC)).const_mul α
    change HasDerivAt (fun z : ℂ => scaledRoot p α z)
      (α * ((p : ℂ) ^ (-s) * Complex.log (p : ℂ) * (-1))) s at h
    have hEq : α * ((p : ℂ) ^ (-s) * Complex.log (p : ℂ) * (-1)) =
        -(Complex.log (p : ℂ) * scaledRoot p α s) := by
      unfold scaledRoot
      ring
    exact hEq ▸ h
  have hDomain : (1 - scaledRoot p α s) ∈ Complex.slitPlane := by
    simpa only [sub_eq_add_neg] using
      Complex.mem_slitPlane_of_norm_lt_one (z := -scaledRoot p α s)
        (by simpa only [norm_neg] using hNorm)
  have hNeg := ((hF.const_sub (1 : ℂ)).clog hDomain).neg
  change HasDerivAt (fun z : ℂ => -Complex.log (1 - scaledRoot p α z)) _ s at hNeg
  simpa only [localLogDerivative, neg_neg] using hNeg

private theorem localLogDerivative_majorant {W σ : ℝ} (hσ : W + 1 < σ) :
    ∃ bound : Primes → ℝ, Summable bound ∧
      ∀ (p : Primes) {α s : ℂ}, ‖α‖ ≤ (p : ℝ) ^ W → σ ≤ s.re →
        ‖localLogDerivative p α s‖ ≤ bound p := by
  let e := W - σ
  let δ := (-1 - e) / 2
  let u := (2 : ℝ) ^ e
  have he : e < -1 := by dsimp [e]; linarith
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have he' : e + δ < -1 := by dsimp [δ]; linarith
  have hu : u < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hGap : 0 < 1 - u := sub_pos.mpr hu
  refine ⟨fun p => (p : ℝ) ^ (e + δ) / (δ * (1 - u)), ?_, ?_⟩
  · exact ((Real.summable_nat_rpow.mpr he').subtype Nat.Prime).div_const (δ * (1 - u))
  intro p α s hα hs
  let z := scaledRoot p α s
  have hp₂ : (2 : ℝ) ≤ p := Nat.cast_le.mpr p.prop.two_le
  have hp : (0 : ℝ) < p := Nat.cast_pos.mpr p.prop.pos
  have hlog₀ : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith)
  have hLog : Real.log (p : ℝ) ≤ (p : ℝ) ^ δ / δ := by
    apply (le_div_iff₀ hδ).2
    rw [mul_comm, ← Real.log_rpow hp]
    exact Real.log_le_self (Real.rpow_nonneg hp.le _)
  have hZ : ‖z‖ ≤ (p : ℝ) ^ e := (scaledRoot_norm_le p hα).trans
    (Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ p) (sub_le_sub_left hs W))
  have hBound : (p : ℝ) ^ e ≤ u :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hp₂ (by linarith)
  have hDenom : 1 - u ≤ ‖(1 : ℂ) - z‖ := by
    calc
      _ ≤ 1 - ‖z‖ := sub_le_sub_left (hZ.trans hBound) _
      _ ≤ _ := by simpa using (norm_sub_norm_le (1 : ℂ) z)
  have hNormLog : ‖Complex.log (p : ℂ)‖ = Real.log (p : ℝ) := by
    rw [← Complex.natCast_log, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog₀]
  change ‖-(Complex.log (p : ℂ) * z / (1 - z))‖ ≤
    (p : ℝ) ^ (e + δ) / (δ * (1 - u))
  rw [norm_neg, norm_div, norm_mul, hNormLog]
  calc
    _ ≤ (Real.log (p : ℝ) * (p : ℝ) ^ e) / (1 - u) :=
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hZ hlog₀) (norm_nonneg _)).trans
        (div_le_div_of_nonneg_left (mul_nonneg hlog₀ (Real.rpow_nonneg hp.le _)) hGap hDenom)
    _ ≤ (((p : ℝ) ^ δ / δ) * (p : ℝ) ^ e) / (1 - u) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hLog (Real.rpow_nonneg hp.le _)) hGap.le
    _ = _ := by
      rw [div_mul_eq_mul_div, div_div, ← Real.rpow_add hp, add_comm δ e]

theorem paper7_dirichlet_log_derivatives_abs_summable
    (α : Primes → ℂ) {s : ℂ} {W : ℝ} (hs : W + 1 < s.re)
    (hα : ∀ p, ‖α p‖ ≤ (p : ℝ) ^ W) :
    Summable (fun p : Primes => ‖localLogDerivative p (α p) s‖) := by
  obtain ⟨bound, hBound, h⟩ := localLogDerivative_majorant hs
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun p => h p (hα p) le_rfl) hBound

/-- The logarithm series with a uniformly bounded number of signed local
factors admits termwise complex differentiation on the Dirichlet half-plane.
Zero roots allow smaller local ranks to be padded to a common finite index. -/
theorem paper7_dirichlet_log_series_hasDeriv {ι : Type*} [Fintype ι]
    (α : ι → Primes → ℂ) (ε : ι → ℂ) (hε : ∀ i, ‖ε i‖ ≤ 1)
    {s : ℂ} {W : ℝ} (hs : W + 1 < s.re)
    (hα : ∀ i p, ‖α i p‖ ≤ (p : ℝ) ^ W) :
    HasDerivAt
      (fun z : ℂ => ∑' p : Primes, ∑ i, ε i * (-Complex.log (1 - scaledRoot p (α i p) z)))
      (∑' p : Primes, ∑ i, ε i * localLogDerivative p (α i p) s) s := by
  classical
  obtain ⟨σ, hσ, hsσ⟩ := exists_between hs
  obtain ⟨bound, hBound, hLocalBound⟩ := localLogDerivative_majorant hσ
  let D : Set ℂ := {z | σ < z.re}
  have hOpen : IsOpen D := isOpen_lt continuous_const Complex.continuous_re
  have hConn : IsPreconnected D :=
    (convex_halfSpace_gt Complex.reLm.isLinear σ).isPreconnected
  have hD : s ∈ D := hsσ
  have hPoint : Summable (fun p : Primes =>
      ∑ i, ε i * (-Complex.log (1 - scaledRoot p (α i p) s))) := by
    apply summable_sum
    intro i _
    exact (paper7_dirichlet_local_logs_summable (α i) hs (hα i)).mul_left (ε i)
  refine hasDerivAt_tsum_of_isPreconnected (hBound.mul_left (Fintype.card ι : ℝ))
    hOpen hConn ?_ ?_ hD hPoint hD
  · intro p z hz
    have hz' : W + 1 < z.re := hσ.trans hz
    exact HasDerivAt.fun_sum fun i _ =>
      (paper7_dirichlet_local_log_hasDeriv p hz' (hα i p)).const_mul (ε i)
  · intro p z hz
    have hz' : σ ≤ z.re := le_of_lt hz
    calc
      ‖∑ i, ε i * localLogDerivative p (α i p) z‖ ≤
          ∑ i, ‖ε i * localLogDerivative p (α i p) z‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _ : ι, bound p := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_mul]
        exact (mul_le_mul_of_nonneg_right (hε i) (norm_nonneg _)).trans
          (by rw [one_mul]; exact hLocalBound p (hα i p) hz')
      _ = (Fintype.card ι : ℝ) * bound p := by simp

/-- The exponentials of the signed local log polynomials have an actual
infinite product in the same half-plane, with a nonzero product value. -/
theorem paper7_dirichlet_scaled_euler_hasProd {ι : Type*} [Fintype ι]
    (α : ι → Primes → ℂ) (ε : ι → ℂ)
    {s : ℂ} {W : ℝ} (hs : W + 1 < s.re)
    (hα : ∀ i p, ‖α i p‖ ≤ (p : ℝ) ^ W) :
    HasProd
      (fun p : Primes =>
        Complex.exp (∑ i, ε i * (-Complex.log (1 - scaledRoot p (α i p) s))))
      (Complex.exp (∑' p : Primes,
        ∑ i, ε i * (-Complex.log (1 - scaledRoot p (α i p) s)))) ∧
    Complex.exp (∑' p : Primes,
      ∑ i, ε i * (-Complex.log (1 - scaledRoot p (α i p) s))) ≠ 0 := by
  classical
  have hPoint : Summable (fun p : Primes =>
      ∑ i, ε i * (-Complex.log (1 - scaledRoot p (α i p) s))) := by
    apply summable_sum
    intro i _
    exact (paper7_dirichlet_local_logs_summable (α i) hs (hα i)).mul_left (ε i)
  exact ⟨by simpa only [Function.comp_apply] using hPoint.hasSum.cexp, Complex.exp_ne_zero _⟩

end

end ManuscriptAudit.DirichletEuler

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.DirichletEuler.paper7_dirichlet_scaled_roots_abs_summable,
      ``ManuscriptAudit.DirichletEuler.paper7_dirichlet_local_logs_summable,
      ``ManuscriptAudit.DirichletEuler.paper7_dirichlet_local_log_hasDeriv,
      ``ManuscriptAudit.DirichletEuler.paper7_dirichlet_log_derivatives_abs_summable,
      ``ManuscriptAudit.DirichletEuler.paper7_dirichlet_log_series_hasDeriv,
      ``ManuscriptAudit.DirichletEuler.paper7_dirichlet_scaled_euler_hasProd] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
