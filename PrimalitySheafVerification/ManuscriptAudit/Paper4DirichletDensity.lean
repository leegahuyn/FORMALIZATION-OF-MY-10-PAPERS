import Lean.Util.CollectAxioms
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import PrimalitySheafVerification.ManuscriptAudit.FiniteSupportDirichletLimit
import PrimalitySheafVerification.ManuscriptAudit.Paper4PrimeDirichletDerivative

/-! The actual Dirichlet density of a reduced residue class is the inverse totient.
The logarithmic singularity is obtained from the derivative of the native prime series. -/

namespace ManuscriptAudit.Paper4DirichletDensity

open Filter Topology
open FiniteSupportDirichletLimit (normalizer normalizer_tendsto)
open Paper4PrimeDirichletDerivative (countCoeff primeDirichletSeries hasDerivAt_primeDirichletSeries)
open Paper4PrimeLogWeightPole (primeSeries bounded_prime_pole_error)

noncomputable section

variable {q : ℕ} [NeZero q] (a : ZMod q)

private abbrev c : ℝ := (q.totient : ℝ)⁻¹

private def regularPart (s : ℝ) : ℝ :=
  primeDirichletSeries a s + c (q := q) * Real.log (s - 1)

private theorem regularPart_eq_sub (s : ℝ) :
    regularPart a s = primeDirichletSeries a s - c (q := q) * normalizer s := by
  rw [regularPart, normalizer, Real.log_inv]
  ring

private theorem regularPart_deriv {s : ℝ} (hs : 1 < s) :
    HasDerivAt (regularPart a) (-primeSeries a s + c (q := q) / (s - 1)) s := by
  have hArg : HasDerivAt (fun x : ℝ ↦ x - 1) 1 s := (hasDerivAt_id s).sub_const 1
  have hLog := (Real.hasDerivAt_log (sub_ne_zero.mpr hs.ne')).comp s hArg
  simpa only [regularPart, Function.comp_apply, mul_one, div_eq_mul_inv] using
    (hasDerivAt_primeDirichletSeries a hs).add (hLog.const_mul (c (q := q)))

/-- After subtracting its explicit logarithm, the actual prime series is bounded
up to the boundary of the real region of absolute convergence. -/
theorem bounded_logarithmic_error (ha : IsUnit a) :
    ∃ B : ℝ, ∀ s ∈ Set.Ioc (1 : ℝ) 2,
      |primeDirichletSeries a s - c (q := q) * normalizer s| ≤ B := by
  obtain ⟨D, hD⟩ := bounded_prime_pole_error a ha
  have hAtTwo : (2 : ℝ) ∈ Set.Ioc 1 2 := ⟨by norm_num, le_rfl⟩
  have hD₀ : 0 ≤ D := (abs_nonneg _).trans (hD 2 hAtTwo)
  have hDerivBound (s : ℝ) (hs : s ∈ Set.Ioc 1 2) :
      ‖-primeSeries a s + c (q := q) / (s - 1)‖ ≤ D := by
    rw [show -primeSeries a s + c (q := q) / (s - 1) =
      -(primeSeries a s - c (q := q) / (s - 1)) by ring, Real.norm_eq_abs, abs_neg]
    exact hD s hs
  refine ⟨D + |regularPart a 2|, fun s hs ↦ ?_⟩
  have hL := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx ↦ (regularPart_deriv a hx.1).hasDerivWithinAt)
    hDerivBound (convex_Ioc (1 : ℝ) 2) hAtTwo hs
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hL
  have hDist : |s - 2| ≤ 1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr hs.2)]
    linarith [hs.1]
  have hNear : |regularPart a s - regularPart a 2| ≤ D :=
    hL.trans ((mul_le_mul_of_nonneg_left hDist hD₀).trans_eq (mul_one D))
  rw [← regularPart_eq_sub a s]
  calc
    |regularPart a s| ≤ |regularPart a s - regularPart a 2| + |regularPart a 2| := by
      convert abs_add_le (regularPart a s - regularPart a 2) (regularPart a 2) using 1 <;> ring
    _ ≤ _ := add_le_add_right hNear _

/-- The genuine prime sum divided by log(1/(s−1)) has the Dirichlet density. -/
theorem normalized_primeSeries_tendsto (ha : IsUnit a) :
    Tendsto (fun s ↦ primeDirichletSeries a s / normalizer s) (𝓝[>] (1 : ℝ))
      (𝓝 (c (q := q))) := by
  obtain ⟨B, hB⟩ := bounded_logarithmic_error a ha
  have hLow : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), 1 < s := self_mem_nhdsWithin
  have hHigh : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), s < 2 :=
    (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2)).filter_mono nhdsWithin_le_nhds
  have hN := normalizer_tendsto.eventually (eventually_gt_atTop (0 : ℝ))
  have hErr : Tendsto (fun s ↦ regularPart a s / normalizer s) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (normalizer_tendsto.const_div_atTop B)
    · exact Eventually.of_forall fun _ ↦ norm_nonneg _
    · filter_upwards [hLow, hHigh, hN] with s hs hUpper hn
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg hn.le, regularPart_eq_sub a]
      exact div_le_div_of_nonneg_right (hB s ⟨hs, hUpper.le⟩) hn.le
  have hSum := hErr.add
    (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ c (q := q)) (𝓝[>] (1 : ℝ)) (𝓝 (c (q := q))))
  rw [zero_add] at hSum
  apply hSum.congr'
  filter_upwards [hN] with s hs
  rw [regularPart_eq_sub a, sub_div, mul_div_cancel_right₀ _ hs.ne']
  ring

/-- Deleting any finite collection of actual matching primes preserves the Dirichlet density. -/
theorem normalized_primeSeries_after_exceptions (ha : IsUnit a) (E : Finset ℕ) :
    Tendsto (fun s ↦ (primeDirichletSeries a s -
      FiniteSupportDirichletLimit.finiteWeight
        (E.filter (fun p ↦ p.Prime ∧ (p : ZMod q) = a)) s) / normalizer s)
      (𝓝[>] (1 : ℝ)) (𝓝 (c (q := q))) := by
  let D := E.filter (fun p ↦ p.Prime ∧ (p : ZMod q) = a)
  have hPos : ∀ p ∈ D, 0 < p := by
    intro p hp
    exact ((Finset.mem_filter.mp hp).2.1).pos
  have h := (normalized_primeSeries_tendsto a ha).sub
    (FiniteSupportDirichletLimit.normalized_finiteWeight_tendsto_zero D hPos)
  rw [sub_zero] at h
  exact h.congr (fun _ ↦ (sub_div _ _ _).symm)

end
end ManuscriptAudit.Paper4DirichletDensity

open Lean Elab Command in
run_cmd do
  for name in [``ManuscriptAudit.Paper4DirichletDensity.bounded_logarithmic_error,
      ``ManuscriptAudit.Paper4DirichletDensity.normalized_primeSeries_tendsto,
      ``ManuscriptAudit.Paper4DirichletDensity.normalized_primeSeries_after_exceptions] do
    let ax ← collectAxioms name
    let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
