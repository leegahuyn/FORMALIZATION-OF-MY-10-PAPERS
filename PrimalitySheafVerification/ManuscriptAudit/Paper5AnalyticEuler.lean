import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper5ActualHasseWeil
import PrimalitySheafVerification.ManuscriptAudit.Paper5ActualEulerRadius
import PrimalitySheafVerification.ManuscriptAudit.DirichletEuler

/-! Prime-dependent analytic Euler convergence with actual cubic point traces. -/

namespace ManuscriptAudit.Paper5AnalyticEuler

open Nat DirichletEuler Paper5ActualHasseWeil EllipticQuadraticRadius
open PrimalitySheafVerification.ManuscriptAudit (paper5TraceCurve)
open scoped BigOperators Topology

noncomputable section

private theorem reciprocal_root_norm {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    {A : ZMod p} (hA : A ≠ 0) {α β : ℂ}
    (hs : α + β = (firstTrace p A : ℂ)) (hm : α * β = (p : ℂ)) :
    ‖α‖ = Real.sqrt (p : ℝ) := by
  have hα : α ≠ 0 := by
    intro hz
    have he : (p : ℂ) = 0 := by simpa [hz] using hm.symm
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) he
  let a := (p : ℝ) + 1 - (Nat.card (paper5TraceCurve p A).toProjective.Point : ℝ)
  have ha : (a : ℂ) = (firstTrace p A : ℂ) := by
    dsimp [a, firstTrace]
    push_cast <;> rfl
  have hRoot : (localPolynomial (p : ℝ) a).IsRoot α⁻¹ := by
    rw [Polynomial.IsRoot, eval_localPolynomial]
    change 1 - (a : ℂ) * α⁻¹ + ((p : ℝ) : ℂ) * (α⁻¹)^2 = 0
    rw [ha, ← hs, Complex.ofReal_natCast, ← hm]
    field_simp [hα] <;> ring
  have h := Paper5ActualEulerRadius.actual_reduced_cubic_roots_on_circle p hp hA α⁻¹ hRoot
  rw [norm_inv, one_div] at h
  exact inv_injective h

theorem exists_actual_roots {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    {A : ZMod p} (hA : A ≠ 0) :
    ∃ α β : ℂ, α + β = (firstTrace p A : ℂ) ∧ α * β = (p : ℂ) ∧
      ‖α‖ = Real.sqrt (p : ℝ) ∧ ‖β‖ = Real.sqrt (p : ℝ) := by
  obtain ⟨α, β, hs, hm⟩ := exist_two_roots (firstTrace p A : ℂ) (p : ℂ)
  exact ⟨α, β, hs, hm, reciprocal_root_norm hp hA hs hm,
    reciprocal_root_norm hp hA (by rwa [add_comm]) (by rwa [mul_comm])⟩

/-- The actual good factors used at p=pₙ, for a single integral parameter A. -/
def Good (A : ℤ) (p : Primes) : Prop :=
  5 ≤ (p : ℕ) ∧ (A : ZMod (p : ℕ)) ≠ 0

def aAt (A : ℤ) (p : Primes) : ℤ :=
  letI : Fact (p : ℕ).Prime := ⟨p.prop⟩
  firstTrace (p : ℕ) (A : ZMod (p : ℕ))

def localFactor (A : ℤ) (p : Primes) (s : ℂ) : ℂ := by
  classical
  exact if Good A p then
    (1 - (aAt A p : ℂ) * (p : ℂ) ^ (-s) + (p : ℂ) * ((p : ℂ) ^ (-s)) ^ 2)⁻¹
  else 1

private def rootPair (A : ℤ) (p : Primes) : ℂ × ℂ := by
  classical
  by_cases hg : Good A p
  · letI : Fact (p : ℕ).Prime := ⟨p.prop⟩
    let h := exists_actual_roots hg.1 hg.2
    exact (Classical.choose h, Classical.choose (Classical.choose_spec h))
  · exact (0, 0)

private theorem rootPair_spec (A : ℤ) (p : Primes) (hg : Good A p) :
    (rootPair A p).1 + (rootPair A p).2 = (aAt A p : ℂ) ∧
    (rootPair A p).1 * (rootPair A p).2 = (p : ℂ) ∧
    ‖(rootPair A p).1‖ = Real.sqrt (p : ℝ) ∧
    ‖(rootPair A p).2‖ = Real.sqrt (p : ℝ) := by
  letI : Fact (p : ℕ).Prime := ⟨p.prop⟩
  let h := exists_actual_roots hg.1 hg.2
  simpa [rootPair, hg, aAt] using Classical.choose_spec (Classical.choose_spec h)

private def root (A : ℤ) (i : Fin 2) (p : Primes) : ℂ :=
  ![(rootPair A p).1, (rootPair A p).2] i

private theorem root_bound (A : ℤ) (i : Fin 2) (p : Primes) :
    ‖root A i p‖ ≤ (p : ℝ) ^ (1 / 2 : ℝ) := by
  rw [← Real.sqrt_eq_rpow]
  by_cases hg : Good A p
  · have h := rootPair_spec A p hg
    fin_cases i
    · change ‖(rootPair A p).1‖ ≤ _
      exact h.2.2.1.le
    · change ‖(rootPair A p).2‖ ≤ _
      exact h.2.2.2.le
  · fin_cases i <;> simp [root, rootPair, hg, Real.sqrt_nonneg]

private theorem one_sub_scaledRoot_ne_zero (A : ℤ) (i : Fin 2) (p : Primes)
    {s : ℂ} (hs : 3 / 2 < s.re) :
    1 - scaledRoot p (root A i p) s ≠ 0 := by
  have hp : (1 : ℝ) < p := by exact_mod_cast p.prop.one_lt
  have h := (scaledRoot_norm_le p (root_bound A i p)).trans_lt
    (Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith : (1 / 2 : ℝ) - s.re < 0))
  intro hz
  have he := (sub_eq_zero.mp hz).symm
  simpa [he] using h

private theorem localFactor_eq_exp (A : ℤ) (p : Primes) {s : ℂ} (hs : 3 / 2 < s.re) :
    Complex.exp (∑ i : Fin 2, (1 : ℂ) * (-Complex.log (1 - scaledRoot p (root A i p) s))) =
      localFactor A p s := by
  have h0 := one_sub_scaledRoot_ne_zero A 0 p hs
  have h1 := one_sub_scaledRoot_ne_zero A 1 p hs
  rw [Fin.sum_univ_two, one_mul, one_mul, Complex.exp_add, Complex.exp_neg,
    Complex.exp_neg, Complex.exp_log h0, Complex.exp_log h1]
  have hInv : (1 - scaledRoot p (root A 0 p) s)⁻¹ * (1 - scaledRoot p (root A 1 p) s)⁻¹ =
      ((1 - scaledRoot p (root A 0 p) s) * (1 - scaledRoot p (root A 1 p) s))⁻¹ := by
    field_simp [h0, h1]
  rw [hInv]
  by_cases hg : Good A p
  · have h := rootPair_spec A p hg
    simp only [localFactor, hg, if_true]
    congr 1
    let T := (p : ℂ) ^ (-s)
    change (1 - (rootPair A p).1 * T) * (1 - (rootPair A p).2 * T) =
      1 - (aAt A p : ℂ) * T + (p : ℂ) * T ^ 2
    linear_combination -T * h.1 + T ^ 2 * h.2.1
  · simp [localFactor, hg, root, rootPair, scaledRoot]

/-- The analytic product of the actual prime-dependent good factors converges
to a nonzero complex value when the real part of s exceeds three halves. -/
theorem actual_euler_hasProd (A : ℤ) {s : ℂ} (hs : 3 / 2 < s.re) :
    ∃ L : ℂ, HasProd (fun p : Primes => localFactor A p s) L ∧ L ≠ 0 := by
  have h := paper7_dirichlet_scaled_euler_hasProd (root A) (fun _ : Fin 2 => 1)
    (show (1 / 2 : ℝ) + 1 < s.re by linarith) (root_bound A)
  exact ⟨_, h.1.congr_fun fun p => (localFactor_eq_exp A p hs).symm, h.2⟩

/-- The logarithmic derivative of the actual local reciprocal polynomial. -/
def logarithmicDerivative (A : ℤ) (p : Primes) (s : ℂ) : ℂ := by
  classical
  let T := (p : ℂ) ^ (-s)
  exact if Good A p then
    Complex.log (p : ℂ) * (-(aAt A p : ℂ) * T + 2 * (p : ℂ) * T^2) /
      (1 - (aAt A p : ℂ) * T + (p : ℂ) * T^2)
  else 0

private theorem sum_root_logarithmic_derivatives (A : ℤ) (p : Primes)
    {s : ℂ} (hs : 3 / 2 < s.re) :
    (∑ i : Fin 2, localLogDerivative p (root A i p) s) = logarithmicDerivative A p s := by
  rw [Fin.sum_univ_two]
  by_cases hg : Good A p
  · let U := scaledRoot p (root A 0 p) s
    let V := scaledRoot p (root A 1 p) s
    let T := (p : ℂ) ^ (-s)
    have h0 : 1 - U ≠ 0 := one_sub_scaledRoot_ne_zero A 0 p hs
    have h1 : 1 - V ≠ 0 := one_sub_scaledRoot_ne_zero A 1 p hs
    have hp := rootPair_spec A p hg
    have hSum : U + V = (aAt A p : ℂ) * T := by
      change (rootPair A p).1 * T + (rootPair A p).2 * T = _
      rw [← add_mul, hp.1]
    have hMul : U * V = (p : ℂ) * T^2 := by
      change ((rootPair A p).1 * T) * ((rootPair A p).2 * T) = _
      rw [← hp.2.1]
      ring
    have hDen : ((1 : ℂ) - U) * (1 - V) =
        1 - (aAt A p : ℂ) * T + (p : ℂ) * T^2 := by
      rw [← hSum, ← hMul]
      ring
    simp only [logarithmicDerivative, hg, if_true]
    calc
      _ = Complex.log (p : ℂ) * (-(U+V) + 2 * (U*V)) / ((1-U)*(1-V)) := by
        change -(Complex.log (p : ℂ) * U / (1-U)) +
          -(Complex.log (p : ℂ) * V / (1-V)) = _
        field_simp [h0,h1] <;> ring
      _ = _ := by rw [hSum, hMul, hDen] <;> ring
  · simp [logarithmicDerivative, hg, localLogDerivative, root, rootPair, scaledRoot]

theorem actual_euler_log_derivatives_abs_summable (A : ℤ) {s : ℂ}
    (hs : 3 / 2 < s.re) :
    Summable (fun p : Primes => ‖logarithmicDerivative A p s‖) := by
  have hσ : (1 / 2 : ℝ) + 1 < s.re := by linarith
  have h0 := paper7_dirichlet_log_derivatives_abs_summable (root A 0) hσ (root_bound A 0)
  have h1 := paper7_dirichlet_log_derivatives_abs_summable (root A 1) hσ (root_bound A 1)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (h0.add h1)
  intro p
  rw [← sum_root_logarithmic_derivatives A p hs, Fin.sum_univ_two]
  exact norm_add_le _ _

private def logSum (A : ℤ) (s : ℂ) : ℂ :=
  ∑' p : Primes, ∑ i : Fin 2, (1 : ℂ) * (-Complex.log (1 - scaledRoot p (root A i p) s))

private theorem actual_tprod_eq_exp_logSum (A : ℤ) {s : ℂ} (hs : 3 / 2 < s.re) :
    (∏' p : Primes, localFactor A p s) = Complex.exp (logSum A s) := by
  have hσ : (1 / 2 : ℝ) + 1 < s.re := by linarith
  have h := paper7_dirichlet_scaled_euler_hasProd (root A) (fun _ : Fin 2 => 1)
    hσ (root_bound A)
  exact (h.1.congr_fun fun p => (localFactor_eq_exp A p hs).symm).tprod_eq

/-- The actual Euler product differentiates in the open absolute-convergence half-plane. -/
theorem actual_euler_hasDerivAt (A : ℤ) {s : ℂ} (hs : 3 / 2 < s.re) :
    HasDerivAt (fun z : ℂ => ∏' p : Primes, localFactor A p z)
      ((∏' p : Primes, localFactor A p s) * (∑' p : Primes, logarithmicDerivative A p s)) s := by
  have hσ : (1 / 2 : ℝ) + 1 < s.re := by linarith
  have h := paper7_dirichlet_log_series_hasDeriv (root A) (fun _ : Fin 2 => 1)
    (fun _ => by simp) hσ (root_bound A)
  have hD : HasDerivAt (logSum A) (∑' p : Primes, logarithmicDerivative A p s) s := by
    change HasDerivAt
      (fun z : ℂ => ∑' p : Primes, ∑ i : Fin 2,
        (1 : ℂ) * (-Complex.log (1 - scaledRoot p (root A i p) z)))
      (∑' p : Primes, logarithmicDerivative A p s) s
    simpa only [one_mul, sum_root_logarithmic_derivatives A _ hs] using h
  have hopen : IsOpen {z : ℂ | (3 / 2 : ℝ) < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hEq : (fun z : ℂ => ∏' p : Primes, localFactor A p z) =ᶠ[𝓝 s]
      (fun z : ℂ => Complex.exp (logSum A z)) := by
    filter_upwards [hopen.mem_nhds hs] with z hz
    exact actual_tprod_eq_exp_logSum A hz
  rw [actual_tprod_eq_exp_logSum A hs]
  exact hD.cexp.congr_of_eventuallyEq hEq

theorem actual_euler_differentiableOn (A : ℤ) :
    DifferentiableOn ℂ (fun z : ℂ => ∏' p : Primes, localFactor A p z)
      {z : ℂ | (3 / 2 : ℝ) < z.re} := by
  intro s hs
  exact (actual_euler_hasDerivAt A hs).differentiableAt.differentiableWithinAt

end
end ManuscriptAudit.Paper5AnalyticEuler

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5AnalyticEuler.actual_euler_hasProd,
      ``ManuscriptAudit.Paper5AnalyticEuler.actual_euler_log_derivatives_abs_summable,
      ``ManuscriptAudit.Paper5AnalyticEuler.actual_euler_hasDerivAt,
      ``ManuscriptAudit.Paper5AnalyticEuler.actual_euler_differentiableOn] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
