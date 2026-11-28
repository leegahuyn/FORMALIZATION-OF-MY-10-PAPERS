import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossContinuationPole
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossRealBoundary

/-! Any genuine pole on the boundary, or in the right half-plane, obstructs the ordinary cutoff. -/

namespace ManuscriptAudit.Paper8OddCrossAnyPole

open Filter Set
open Paper8OddCrossAbelObstruction Paper8OddCrossContinuationPole Paper8OddCrossRealBoundary
open scoped Topology

noncomputable section

private theorem no_zero_scaled_limit_at_pole {P : ℂ → ℂ} {c : ℂ}
    (hM : MeromorphicAt P c) (hPole : meromorphicOrderAt P c < 0)
    (hZero : Tendsto (fun ε : ℝ => (ε : ℂ) * P ((ε : ℂ) + c)) (𝓝[>] 0) (𝓝 0)) : False := by
  have hTop : meromorphicOrderAt P c ≠ ⊤ := ne_of_lt (hPole.trans_le le_top)
  let d : ℤ := (meromorphicOrderAt P c).untop₀
  have hCast : (d : WithTop ℤ) = meromorphicOrderAt P c :=
    WithTop.coe_untop₀_of_ne_top hTop
  have hd : d < 0 := by
    have h' : (d : WithTop ℤ) < 0 := by rw [hCast]; exact hPole
    exact_mod_cast h'
  obtain ⟨n, hn⟩ : ∃ n : ℕ, d = -((n + 1 : ℕ) : ℤ) := by
    cases he : d with
    | ofNat n => omega
    | negSucc n => exact ⟨n, rfl⟩
  have hO : meromorphicOrderAt P c = (-((n + 1 : ℕ) : ℤ) : ℤ) := by
    rw [← hCast, hn]
  obtain ⟨g, hg, hg₀, hEq⟩ := (meromorphicOrderAt_eq_int_iff hM).1 hO
  have hε : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Complex.ofReal_zero] using Complex.continuous_ofReal.continuousAt.tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hPowerZero : Tendsto (fun ε : ℝ => (ε : ℂ) ^ (n + 1) * P ((ε : ℂ) + c))
      (𝓝[>] 0) (𝓝 0) := by
    have hZ := hZero.mul (hε.pow n)
    refine (show Tendsto (fun ε : ℝ => ((ε : ℂ) * P ((ε : ℂ) + c)) * (ε : ℂ) ^ n)
      (𝓝[>] 0) (𝓝 0) by simpa only [zero_mul] using hZ).congr' (Eventually.of_forall fun ε => ?_)
    rw [pow_succ]
    ring
  have hRad := cross_right_radial_tendsto c
  have hG : Tendsto (fun ε : ℝ => g ((ε : ℂ) + c)) (𝓝[>] 0) (𝓝 (g c)) :=
    hg.continuousAt.tendsto.comp (hRad.mono_right nhdsWithin_le_nhds)
  have hPowerG : Tendsto (fun ε : ℝ => (ε : ℂ) ^ (n + 1) * P ((ε : ℂ) + c))
      (𝓝[>] 0) (𝓝 (g c)) := by
    refine hG.congr' ?_
    filter_upwards [hRad.eventually hEq, (self_mem_nhdsWithin : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε)]
      with ε he hε
    change P ((ε : ℂ) + c) = ((ε : ℂ) + c - c) ^ (-((n + 1 : ℕ) : ℤ)) • g ((ε : ℂ) + c) at he
    rw [he, add_sub_cancel_right, zpow_neg, zpow_natCast, smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hε.ne')), one_mul]
  exact hg₀ (tendsto_nhds_unique hPowerG hPowerZero)

theorem no_ordered_cross_limit_of_continuation_boundary_pole {P : ℂ → ℂ} {U : Set ℂ}
    (hP : AnalyticOnNhd ℂ P U) (hU : IsPreconnected U) (hRight : U ⊆ {w : ℂ | 0 < w.re})
    {w₀ : ℂ} (h₀ : w₀ ∈ U) (h₁ : 1 < w₀.re)
    (hInitial : EqOn P crossShiftedDirichletSeries {w : ℂ | 1 < w.re}) (τ : ℝ)
    (hApproach : ∀ᶠ ε : ℝ in 𝓝[>] 0, (ε : ℂ) + (τ : ℂ) * Complex.I ∈ U)
    (hM : MeromorphicAt P ((τ : ℂ) * Complex.I))
    (hPole : meromorphicOrderAt P ((τ : ℂ) * Complex.I) < 0) :
    ¬ ∃ L : ℂ, Tendsto orderedCrossCutoff atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  have hA := cross_continuation_agrees_with_abel_of_ordered_limit hL hP hU hRight h₀ h₁ hInitial
  apply no_zero_scaled_limit_at_pole hM hPole
  refine (ordered_cross_cutoff_forces_zero_at_every_abel_boundary hL τ).congr' ?_
  filter_upwards [hApproach] with ε hε
  rw [hA hε]

theorem no_ordered_cross_limit_of_continuation_interior_pole {P : ℂ → ℂ} {U : Set ℂ}
    (hP : AnalyticOnNhd ℂ P U) (hU : IsPreconnected U) (hRight : U ⊆ {w : ℂ | 0 < w.re})
    {w₀ : ℂ} (h₀ : w₀ ∈ U) (h₁ : 1 < w₀.re)
    (hInitial : EqOn P crossShiftedDirichletSeries {w : ℂ | 1 < w.re})
    {c : ℂ} (hc : 0 < c.re) (hNear : ∀ᶠ w in 𝓝[≠] c, w ∈ U)
    (hPole : meromorphicOrderAt P c < 0) :
    ¬ ∃ L : ℂ, Tendsto orderedCrossCutoff atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  have hA := cross_continuation_agrees_with_abel_of_ordered_limit hL hP hU hRight h₀ h₁ hInitial
  have hEq : P =ᶠ[𝓝[≠] c] crossAbelShiftedZeta := hNear.mono fun _ hw => hA hw
  have hcA := crossAbelShiftedZeta_analyticOnNhd_of_ordered_limit hL c hc
  rw [meromorphicOrderAt_congr hEq] at hPole
  exact (not_lt_of_ge hcA.meromorphicOrderAt_nonneg) hPole

end
end ManuscriptAudit.Paper8OddCrossAnyPole

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8OddCrossAnyPole.no_ordered_cross_limit_of_continuation_boundary_pole,
      ``ManuscriptAudit.Paper8OddCrossAnyPole.no_ordered_cross_limit_of_continuation_interior_pole] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
