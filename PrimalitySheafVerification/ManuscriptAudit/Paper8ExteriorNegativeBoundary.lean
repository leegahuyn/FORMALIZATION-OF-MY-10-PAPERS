import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8ExteriorNegativeRadius

/-! The p. 314 literal outside branch has no continuous extension at the negative unit point. -/

namespace ManuscriptAudit.Paper8ExteriorNegativeBoundary

open Filter Set Paper8ExteriorComplex Paper8ExteriorNegativeRadius
open scoped Topology

theorem no_continuous_extension_at_negative_one {F : ℂ → ℂ}
    (hCont : ContinuousAt F (-1 : ℂ))
    (hAgree : ∀ᶠ q in 𝓝[Metric.ball (0 : ℂ) 1] (-1 : ℂ), F q = exterior q) : False := by
  obtain ⟨δ, hδ, hNear⟩ := Metric.continuousAt_iff.mp hCont 1 zero_lt_one
  have hAgreement : {q : ℂ | q ∈ Metric.ball (0 : ℂ) 1 → F q = exterior q} ∈ 𝓝 (-1 : ℂ) :=
    eventually_nhdsWithin_iff.mp hAgree
  obtain ⟨ρ, hρ, hLocal⟩ := Metric.mem_nhds_iff.mp hAgreement
  let A : ℝ := |(F (-1)).re| + 2
  have hA : 0 < A := by dsimp [A]; positivity
  let e : ℝ := min (δ / 2) (min (ρ / 2) (min (1 / 4) (1 / A)))
  have he : 0 < e :=
    lt_min (div_pos hδ (by norm_num))
      (lt_min (div_pos hρ (by norm_num)) (lt_min (by norm_num) (one_div_pos.mpr hA)))
  have hδe : e ≤ δ / 2 := min_le_left _ _
  have hρe : e ≤ ρ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have heSmall : e ≤ 1 / 4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have heInv : e ≤ 1 / A := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let r : ℝ := 1 - e
  have hr0 : 0 ≤ r := by dsimp [r]; linarith only [heSmall]
  have hr1 : r < 1 := by dsimp [r]; linarith only [he]
  have hOneSub : 1 - r = e := by dsimp [r]; ring
  let q : ℂ := -(r : ℂ)
  have hDiff : q - (-1 : ℂ) = (e : ℂ) := by
    change -(r : ℂ) - (-1 : ℂ) = (e : ℂ)
    calc
      _ = (((1 : ℝ) - r : ℝ) : ℂ) := by
        rw [Complex.ofReal_sub, Complex.ofReal_one]
        ring
      _ = (e : ℂ) := congrArg Complex.ofReal hOneSub
  have hDist : dist q (-1 : ℂ) = e := by
    rw [dist_eq_norm, hDiff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos he]
  have hClose : ‖F q - F (-1)‖ < 1 := by
    rw [← dist_eq_norm]
    apply hNear
    rw [hDist]
    linarith only [hδ, hδe]
  have hInside : q ∈ Metric.ball (0 : ℂ) 1 := by
    simpa only [q, Metric.mem_ball, dist_zero_right, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hEq : F q = exterior q :=
    hLocal (by rw [Metric.mem_ball, hDist]; linarith only [hρ, hρe]) hInside
  have hUpper : (F q).re ≤ 1 - r / (2 * (1 - r) ^ 2) := by
    rw [hEq]
    exact negative_radial_upper hr0 hr1
  have hEA : e * A ≤ 1 := (le_div_iff₀ hA).mp heInv
  have hMul : A * (2 * e ^ 2) ≤ r := by
    calc
      _ = (e * A) * (2 * e) := by ring
      _ ≤ 1 * (1 / 2) := mul_le_mul hEA (by linarith only [heSmall]) (by positivity) zero_le_one
      _ ≤ r := by dsimp [r]; linarith only [heSmall]
  have hRatio : A ≤ r / (2 * (1 - r) ^ 2) := by
    rw [hOneSub]
    exact (le_div_iff₀ (by positivity)).mpr hMul
  have hLower : -((F q).re - (F (-1)).re) ≤ ‖F q - F (-1)‖ := by
    rw [← Complex.sub_re]
    exact (neg_le_abs _).trans (Complex.abs_re_le_norm _)
  have hCenter : -(|(F (-1)).re|) ≤ (F (-1)).re := by
    simpa only [neg_neg] using (neg_le_neg (neg_le_abs (F (-1)).re))
  dsimp [A] at hRatio
  linarith only [hUpper, hRatio, hClose, hLower, hCenter]

/-- A continuous, nonzero choice of the fractional factor does not remove the obstruction. -/
theorem no_continuous_weighted_extension_at_negative_one {G root : ℂ → ℂ}
    (hCont : ContinuousAt G (-1 : ℂ)) (hRoot : ContinuousAt root (-1 : ℂ))
    (hNonzero : root (-1) ≠ 0)
    (hAgree : ∀ᶠ q in 𝓝[Metric.ball (0 : ℂ) 1] (-1 : ℂ), G q = root q * exterior q) :
    False := by
  refine no_continuous_extension_at_negative_one (hCont.div hRoot hNonzero) ?_
  have hMem : root (-1) ∈ {z : ℂ | z ≠ 0} := hNonzero
  have hNear : ∀ᶠ q in 𝓝 (-1 : ℂ), root q ≠ 0 :=
    hRoot (isOpen_ne.mem_nhds hMem)
  have hWithin : ∀ᶠ q in 𝓝[Metric.ball (0 : ℂ) 1] (-1 : ℂ), root q ≠ 0 :=
    hNear.filter_mono nhdsWithin_le_nhds
  filter_upwards [hAgree, hWithin] with q hEq hNe
  change G q / root q = exterior q
  exact (div_eq_iff hNe).mpr (hEq.trans (mul_comm _ _))

end ManuscriptAudit.Paper8ExteriorNegativeBoundary

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ExteriorNegativeBoundary.no_continuous_extension_at_negative_one,
      ``ManuscriptAudit.Paper8ExteriorNegativeBoundary.no_continuous_weighted_extension_at_negative_one] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
