import Lean.Util.CollectAxioms
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.AtTopBot.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.Field

/-!
# Curvature and mass do not bound the Sobolev norm before a gauge condition

Paper 10, physical PDF p. 470, Proposition 3.1. On the flat periodic
coordinate box of periods `2π` and `1`, exact abelian forms can minimize the
curvature-plus-mass energy while their first derivatives diverge in L².
All norms below are the actual integrals of the coordinate squares.
-/

namespace ManuscriptAudit.PeriodicExactGauge

open Filter
open scoped Topology

noncomputable section

abbrev Field2 := ℝ → ℝ → ℝ

structure OneForm where
  dx : Field2
  dy : Field2

def partialX (f : Field2) (x y : ℝ) : ℝ := deriv (fun t => f t y) x

def partialY (f : Field2) (x y : ℝ) : ℝ := deriv (f x) y

def exteriorDerivative (f : Field2) : OneForm := ⟨partialX f, partialY f⟩

def curvature (a : OneForm) (x y : ℝ) : ℝ :=
  partialX a.dy x y - partialY a.dx x y

def integrate (f : Field2) : ℝ :=
  ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..(2 * Real.pi), f x y

def mass (a : OneForm) : ℝ :=
  integrate (fun x y => a.dx x y ^ 2 + a.dy x y ^ 2)

def derivativeNormSquare (a : OneForm) : ℝ :=
  integrate (fun x y =>
    partialX a.dx x y ^ 2 + partialY a.dx x y ^ 2 +
      partialX a.dy x y ^ 2 + partialY a.dy x y ^ 2)

def sobolevNormSquare (a : OneForm) : ℝ := mass a + derivativeNormSquare a

def energy (a : OneForm) : ℝ := integrate (fun x y => curvature a x y ^ 2) + mass a

def rate (n : ℕ) : ℝ := ((n + 1 : ℕ) : ℝ)

def frequency (n : ℕ) : ℕ := (n + 1) ^ 2

private theorem frequency_pos (n : ℕ) : 0 < frequency n := by
  unfold frequency
  exact pow_pos (Nat.succ_pos _) _

private theorem rate_pos (n : ℕ) : 0 < rate n := by
  unfold rate
  exact_mod_cast Nat.succ_pos n

private theorem frequency_cast (n : ℕ) : (frequency n : ℝ) = rate n ^ 2 := by
  simp [frequency, rate]

def mode (n : ℕ) : OneForm :=
  ⟨fun x _ => (rate n)⁻¹ * Real.sin ((frequency n : ℝ) * x), fun _ _ => 0⟩

def potential (n : ℕ) : Field2 :=
  fun x _ => -((rate n) ^ 3)⁻¹ * Real.cos ((frequency n : ℝ) * x)

theorem mode_smooth (n : ℕ) :
    ContDiff ℝ ⊤ (Function.uncurry (mode n).dx) ∧
      ContDiff ℝ ⊤ (Function.uncurry (mode n).dy) := by
  constructor
  · change ContDiff ℝ ⊤ (fun z : ℝ × ℝ =>
      (rate n)⁻¹ * Real.sin ((frequency n : ℝ) * z.1))
    fun_prop
  · change ContDiff ℝ ⊤ (fun _ : ℝ × ℝ => (0 : ℝ))
    fun_prop

theorem potential_smooth (n : ℕ) : ContDiff ℝ ⊤ (Function.uncurry (potential n)) := by
  change ContDiff ℝ ⊤ (fun z : ℝ × ℝ =>
    -((rate n) ^ 3)⁻¹ * Real.cos ((frequency n : ℝ) * z.1))
  fun_prop

theorem mode_periodic (n : ℕ) (x y : ℝ) :
    Function.Periodic (fun t => (mode n).dx t y) (2 * Real.pi) ∧
    Function.Periodic (fun t => (mode n).dy t y) (2 * Real.pi) ∧
    Function.Periodic ((mode n).dx x) 1 ∧ Function.Periodic ((mode n).dy x) 1 := by
  refine ⟨?_, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  intro t
  change (rate n)⁻¹ * Real.sin ((frequency n : ℝ) * (t + 2 * Real.pi)) =
    (rate n)⁻¹ * Real.sin ((frequency n : ℝ) * t)
  rw [mul_add, Real.sin_add_nat_mul_two_pi]

theorem potential_periodic (n : ℕ) (x y : ℝ) :
    Function.Periodic (fun t => potential n t y) (2 * Real.pi) ∧
      Function.Periodic (potential n x) 1 := by
  refine ⟨?_, fun _ => rfl⟩
  intro t
  unfold potential
  rw [mul_add, Real.cos_add_nat_mul_two_pi]

private theorem frequency_derivative (n : ℕ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => (frequency n : ℝ) * t) (frequency n : ℝ) x := by
  simpa only [mul_one] using (hasDerivAt_id' x).const_mul (frequency n : ℝ)

private theorem potential_dx (n : ℕ) (x y : ℝ) :
    partialX (potential n) x y = (mode n).dx x y := by
  have h := ((frequency_derivative n x).cos).const_mul (-((rate n)^3)⁻¹)
  change deriv (fun t => -((rate n)^3)⁻¹ * Real.cos ((frequency n : ℝ) * t)) x =
    (rate n)⁻¹ * Real.sin ((frequency n : ℝ) * x)
  rw [h.deriv, frequency_cast]
  field_simp [(rate_pos n).ne'] <;> ring

theorem mode_exact (n : ℕ) : mode n = exteriorDerivative (potential n) := by
  unfold mode exteriorDerivative
  congr 1
  · funext x y
    exact (potential_dx n x y).symm
  · funext x y
    simp [partialY, potential]

private theorem mode_dx_x (n : ℕ) (x y : ℝ) :
    partialX (mode n).dx x y = rate n * Real.cos ((frequency n : ℝ) * x) := by
  have h := ((frequency_derivative n x).sin).const_mul (rate n)⁻¹
  change deriv (fun t => (rate n)⁻¹ * Real.sin ((frequency n : ℝ) * t)) x =
    rate n * Real.cos ((frequency n : ℝ) * x)
  rw [h.deriv, frequency_cast]
  field_simp [(rate_pos n).ne'] <;> ring

private theorem mode_dx_y (n : ℕ) (x y : ℝ) : partialY (mode n).dx x y = 0 := by
  simp [partialY, mode]

private theorem mode_dy_x (n : ℕ) (x y : ℝ) : partialX (mode n).dy x y = 0 := by
  simp [partialX, mode]

private theorem mode_dy_y (n : ℕ) (x y : ℝ) : partialY (mode n).dy x y = 0 := by
  simp [partialY, mode]

theorem mode_flat (n : ℕ) (x y : ℝ) : curvature (mode n) x y = 0 := by
  simp [curvature, mode_dy_x, mode_dx_y]

private theorem integrate_x (f : ℝ → ℝ) :
    integrate (fun x _ => f x) = ∫ x in (0 : ℝ)..(2 * Real.pi), f x := by
  simp [integrate, intervalIntegral.integral_const]

private theorem trig_squares_integral (k : ℕ) (hk : 0 < k) :
    (∫ x in (0 : ℝ)..(2 * Real.pi), Real.sin ((k : ℝ) * x) ^ 2) = Real.pi ∧
    (∫ x in (0 : ℝ)..(2 * Real.pi), Real.cos ((k : ℝ) * x) ^ 2) = Real.pi := by
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  have hz : Real.sin ((k : ℝ) * (2 * Real.pi)) = 0 := by
    simpa only [zero_add, Real.sin_zero] using Real.sin_add_nat_mul_two_pi 0 k
  constructor
  · apply mul_left_cancel₀ hk'.ne'
    rw [intervalIntegral.mul_integral_comp_mul_left (f := fun x => Real.sin x ^ 2),
      mul_zero, integral_sin_sq, Real.sin_zero, hz]
    ring
  · apply mul_left_cancel₀ hk'.ne'
    rw [intervalIntegral.mul_integral_comp_mul_left (f := fun x => Real.cos x ^ 2),
      mul_zero, integral_cos_sq, Real.sin_zero, hz]
    ring

theorem mode_mass (n : ℕ) : mass (mode n) = Real.pi / (rate n) ^ 2 := by
  change integrate (fun x _ =>
    ((rate n)⁻¹ * Real.sin ((frequency n : ℝ) * x)) ^ 2 + (0 : ℝ) ^ 2) = _
  simp only [show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero, integrate_x, mul_pow]
  rw [intervalIntegral.integral_const_mul, (trig_squares_integral _ (frequency_pos n)).1,
    div_eq_mul_inv, inv_pow]
  ring

theorem mode_derivativeNormSquare (n : ℕ) :
    derivativeNormSquare (mode n) = (rate n) ^ 2 * Real.pi := by
  unfold derivativeNormSquare
  simp only [mode_dx_x, mode_dx_y, mode_dy_x, mode_dy_y,
    show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero, integrate_x, mul_pow]
  rw [intervalIntegral.integral_const_mul, (trig_squares_integral _ (frequency_pos n)).2]

private theorem integrate_nonneg (f : Field2) (hf : ∀ x y, 0 ≤ f x y) :
    0 ≤ integrate f := by
  unfold integrate
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro y _
  apply intervalIntegral.integral_nonneg (by positivity)
  intro x _
  exact hf x y

theorem mass_nonneg (a : OneForm) : 0 ≤ mass a :=
  integrate_nonneg _ (fun _ _ => add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem energy_nonneg (a : OneForm) : 0 ≤ energy a :=
  add_nonneg (integrate_nonneg _ (fun _ _ => sq_nonneg _)) (mass_nonneg a)

theorem zero_form_minimizes : energy ⟨fun _ _ => 0, fun _ _ => 0⟩ = 0 := by
  simp [energy, mass, integrate, curvature, partialX, partialY]

theorem mode_energy_eq_mass (n : ℕ) : energy (mode n) = mass (mode n) := by
  simp [energy, mode_flat, integrate]

theorem mode_energy_le_pi (n : ℕ) : energy (mode n) ≤ Real.pi := by
  rw [mode_energy_eq_mass, mode_mass, div_le_iff₀ (sq_pos_of_pos (rate_pos n))]
  have hn : (1 : ℝ) ≤ rate n := by
    unfold rate
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hsq : (1 : ℝ) ≤ rate n ^ 2 := by
    simpa only [one_mul, pow_two] using
      mul_le_mul hn hn (by norm_num : (0 : ℝ) ≤ 1) (rate_pos n).le
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hsq Real.pi_pos.le

private theorem rate_tends_to_atTop : Tendsto rate atTop atTop := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  apply tendsto_atTop.2
  intro B
  filter_upwards [tendsto_atTop.1 hn B] with n hn'
  exact hn'.trans (by unfold rate; exact_mod_cast Nat.le_succ n)

private theorem rate_square_tends_to_atTop :
    Tendsto (fun n => rate n ^ 2) atTop atTop :=
  (tendsto_pow_atTop (n := 2) (by decide)).comp rate_tends_to_atTop

theorem mode_energy_tends_to_minimum : Tendsto (fun n => energy (mode n)) atTop (𝓝 0) := by
  have hinv : Tendsto (fun n => (rate n ^ 2)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).comp
      rate_square_tends_to_atTop
  have hconst : Tendsto (fun _ : ℕ => Real.pi) atTop (𝓝 Real.pi) := tendsto_const_nhds
  simpa only [mode_energy_eq_mass, mode_mass, div_eq_mul_inv, mul_zero] using hconst.mul hinv

theorem mode_derivative_norm_tends_to_atTop :
    Tendsto (fun n => derivativeNormSquare (mode n)) atTop atTop := by
  apply tendsto_atTop.2
  intro B
  filter_upwards [tendsto_atTop.1 rate_square_tends_to_atTop (B / Real.pi)] with n hn
  rw [mode_derivativeNormSquare]
  exact (div_le_iff₀ Real.pi_pos).mp hn

/-- Every subsequence has arbitrarily large squared Sobolev norm, despite
the original sequence minimizing the nonnegative curvature-plus-mass energy. -/
theorem no_subsequence_bounded_in_sobolev_norm (s : ℕ → ℕ) (hs : StrictMono s) :
    ¬ ∃ B : ℝ, ∀ n, sobolevNormSquare (mode (s n)) ≤ B := by
  rintro ⟨B, hB⟩
  have ht : Tendsto s atTop atTop := hs.tendsto_atTop
  obtain ⟨n, hn⟩ := (tendsto_atTop.1 (mode_derivative_norm_tends_to_atTop.comp ht) (B + 1)).exists
  have hmass := mass_nonneg (mode (s n))
  have hbound := hB n
  change B + 1 ≤ derivativeNormSquare (mode (s n)) at hn
  unfold sobolevNormSquare at hbound
  linarith

end

end ManuscriptAudit.PeriodicExactGauge

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.PeriodicExactGauge.mode_exact,
      ``ManuscriptAudit.PeriodicExactGauge.mode_flat,
      ``ManuscriptAudit.PeriodicExactGauge.mode_smooth,
      ``ManuscriptAudit.PeriodicExactGauge.mode_periodic,
      ``ManuscriptAudit.PeriodicExactGauge.potential_periodic,
      ``ManuscriptAudit.PeriodicExactGauge.mode_energy_le_pi,
      ``ManuscriptAudit.PeriodicExactGauge.zero_form_minimizes,
      ``ManuscriptAudit.PeriodicExactGauge.mode_energy_tends_to_minimum,
      ``ManuscriptAudit.PeriodicExactGauge.mode_derivative_norm_tends_to_atTop,
      ``ManuscriptAudit.PeriodicExactGauge.no_subsequence_bounded_in_sobolev_norm] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
