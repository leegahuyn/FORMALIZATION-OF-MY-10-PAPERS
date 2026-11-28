import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.HyperbolicCuspGaugeTest

/-! The full Dirichlet trace condition on smooth co-closed forms is not
closed in the actual width-two cusp L² metric. -/

namespace ManuscriptAudit.Paper10CoulombTraceClosure

open MeasureTheory Set
open Paper10CoulombMultiplier Paper10CoulombProductRule
open scoped ContDiff Interval

noncomputable section

def limitProfile (y : ℝ) : ℝ := Real.smoothTransition (y - 4)
def nearBoundary (n : ℕ) (y : ℝ) : ℝ :=
  Real.smoothTransition (((n : ℝ) + 1) * (6 - y) - 1)
def approximation (n : ℕ) (y : ℝ) : ℝ := limitProfile y * nearBoundary n y

def horizontalForm (u : ℝ → ℝ) : OneForm := fun _ y ↦ (u y, 0)

theorem horizontal_coclosed (u : ℝ → ℝ) (x y : ℝ) :
    codifferential (horizontalForm u) x y = 0 := by
  rw [codifferential_eq_coordinateDivergence]
  simp [horizontalForm]

theorem profiles_smooth (n : ℕ) : ContDiff ℝ ∞ limitProfile ∧ ContDiff ℝ ∞ (approximation n) := by
  have h : ContDiff ℝ ∞ limitProfile :=
    Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)
  have hN : ContDiff ℝ ∞ (nearBoundary n) :=
    Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul (contDiff_const.sub contDiff_id)).sub contDiff_const)
  exact ⟨h, h.mul hN⟩

theorem limit_nonzero_trace : limitProfile 6 = 1 :=
  Real.smoothTransition.one_of_one_le (by norm_num)

theorem approximate_zero_near_trace (n : ℕ) (y : ℝ)
    (hy : 6 - 1 / ((n : ℝ) + 1) ≤ y) : approximation n y = 0 := by
  have hN : 0 < (n : ℝ) + 1 := by positivity
  have h : (n + 1 : ℝ) * (6 - y) ≤ 1 := by
    have hy' : 6 - y ≤ 1 / ((n : ℝ) + 1) := by linarith
    exact (mul_comm _ _).trans_le ((le_div_iff₀ hN).mp hy')
  rw [approximation, nearBoundary, Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr h), mul_zero]

private def err (n : ℕ) (y : ℝ) : ℝ := (limitProfile y - approximation n y)^2

/-- Upper-half-plane one-form metric and area factors cancel. The remaining
factor two is the actual cusp width. -/
def nativeDistanceSquared (n : ℕ) : ℝ := 2 * ∫ y : ℝ in 4..6, err n y

theorem native_distance_squared_le (n : ℕ) :
    nativeDistanceSquared n ≤ 4 / ((n : ℝ)+1) := by
  let a : ℝ := 6 - 2 / ((n : ℝ)+1)
  have hN : 0 < (n : ℝ)+1 := by positivity
  have hN1 : 1 ≤ (n : ℝ)+1 := by
    have h0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hA : 4 ≤ a := by
    dsimp only [a]
    have h : 2 / ((n : ℝ)+1) ≤ 2 := (div_le_iff₀ hN).mpr (by nlinarith)
    linarith
  have hB : a ≤ 6 := by dsimp only [a]; linarith [div_nonneg (by norm_num : (0:ℝ) ≤ 2) hN.le]
  have hc : Continuous (err n) := ((profiles_smooth n).1.continuous.sub
    (profiles_smooth n).2.continuous).pow 2
  have hZ : (∫ y : ℝ in 4..a, err n y) = 0 := by
    rw [intervalIntegral.integral_congr (show ∀ y ∈ uIcc 4 a, err n y = (fun _ : ℝ ↦ 0) y from ?_)]
    · simp
    · intro y hy
      have hY : 2 / ((n : ℝ)+1) ≤ 6 - y := by
        rw [uIcc_of_le hA] at hy
        linarith [hy.2]
      have hMul : 2 ≤ ((n : ℝ)+1) * (6-y) := by
        simpa only [mul_comm] using (div_le_iff₀ hN).mp hY
      have hT : nearBoundary n y = 1 :=
        Real.smoothTransition.one_of_one_le (by linarith)
      simp [err, approximation, hT]
  have hBound (y : ℝ) : err n y ≤ 1 := by
    have p0 : 0 ≤ limitProfile y := Real.smoothTransition.nonneg _
    have p1 : limitProfile y ≤ 1 := Real.smoothTransition.le_one _
    have q0 : 0 ≤ nearBoundary n y := Real.smoothTransition.nonneg _
    have q1 : nearBoundary n y ≤ 1 := Real.smoothTransition.le_one _
    let t := limitProfile y - approximation n y
    have ht0 : 0 ≤ t := sub_nonneg.mpr (mul_le_of_le_one_right p0 q1)
    have ht1 : t ≤ 1 := (sub_le_self _ (mul_nonneg p0 q0)).trans p1
    change t^2 ≤ 1
    nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht1)]
  have hC := intervalIntegral.integral_mono_on hB (hc.intervalIntegrable (μ := volume) a 6)
    ((continuous_const : Continuous (fun _ : ℝ ↦ (1 : ℝ))).intervalIntegrable (μ := volume) a 6) (fun y _ ↦ hBound y)
  rw [intervalIntegral.integral_const] at hC
  norm_num at hC
  have hSplit := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) 4 a) (hc.intervalIntegrable (μ := volume) a 6)
  rw [hZ, zero_add] at hSplit
  rw [nativeDistanceSquared, ← hSplit]
  dsimp only [a] at hC
  linarith

/-- For arbitrarily small actual L² error there is a smooth, co-closed,
zero-trace approximant to the smooth form with nonzero trace. -/
theorem native_arbitrarily_close (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, nativeDistanceSquared n < ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (4 / ε)
  have hn' : 4 / ε < (n : ℝ) + 1 := hn.trans (by linarith)
  have h : 4 / ((n : ℝ)+1) < ε := by
    apply (div_lt_iff₀ (by positivity : 0 < (n : ℝ)+1)).mpr
    have h' := (div_lt_iff₀ hε).mp hn'
    rwa [mul_comm] at h'
  exact ⟨n, (native_distance_squared_le n).trans_lt h⟩

end
end ManuscriptAudit.Paper10CoulombTraceClosure

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.Paper10CoulombTraceClosure.horizontal_coclosed,
      ``ManuscriptAudit.Paper10CoulombTraceClosure.profiles_smooth,
      ``ManuscriptAudit.Paper10CoulombTraceClosure.limit_nonzero_trace,
      ``ManuscriptAudit.Paper10CoulombTraceClosure.approximate_zero_near_trace,
      ``ManuscriptAudit.Paper10CoulombTraceClosure.native_distance_squared_le,
      ``ManuscriptAudit.Paper10CoulombTraceClosure.native_arbitrarily_close] do
    let ax ← collectAxioms name
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
