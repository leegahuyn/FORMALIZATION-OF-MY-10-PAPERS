import Lean.Util.CollectAxioms
import Mathlib.Analysis.Complex.RemovableSingularity
import PrimalitySheafVerification.ManuscriptAudit.Paper8ExteriorComplexHolomorphy

/-!
# The branched exterior normalization cannot descend to a punctured disk

A holomorphic twenty-fourth root of the coordinate on a punctured disk would
extend continuously by zero, then holomorphically. Its twenty-fourth power
would have derivative zero at zero, contrary to the identity map. The same
argument applies to the weighted outside series after dividing by the
unweighted series near zero.
-/

namespace ManuscriptAudit.Paper8ExteriorBranchObstruction

open Filter Set Paper8InsideComplexAnalytic Paper8ExteriorComplex Paper8ExteriorComplexHolomorphy
open scoped Topology

noncomputable section

theorem no_holomorphic_root_on_punctured_disk {r : ℝ} (hr : 0 < r) {b : ℂ → ℂ}
    (hDiff : DifferentiableOn ℂ b (Metric.ball (0 : ℂ) r \ {0}))
    (hRoot : ∀ z ∈ Metric.ball (0 : ℂ) r \ {0}, b z ^ (24 : ℕ) = z) : False := by
  let F : ℂ → ℂ := fun z => if z = 0 then 0 else b z
  have hF0 : F 0 = 0 := by simp [F]
  have hEq (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) r) : F z ^ (24 : ℕ) = z := by
    by_cases h : z = 0
    · subst z
      simp [hF0]
    · simpa [F, h] using hRoot z ⟨hz, by simpa using h⟩
  have hContinuous : ContinuousAt F 0 := by
    refine Metric.continuousAt_iff.mpr ?_
    intro ε hε
    refine ⟨min r (ε ^ (24 : ℕ)), lt_min hr (pow_pos hε _), ?_⟩
    intro z hz
    have hNorm : ‖z‖ < min r (ε ^ (24 : ℕ)) := by
      simpa only [dist_zero_right] using hz
    have hz' : z ∈ Metric.ball (0 : ℂ) r := by
      simpa [Metric.mem_ball, dist_zero_right] using hNorm.trans_le (min_le_left _ _)
    have hPow : ‖F z‖ ^ (24 : ℕ) = ‖z‖ := by rw [← norm_pow, hEq z hz']
    rw [hF0, dist_zero_right]
    by_contra! h
    have hLe := pow_le_pow_left₀ hε.le h (24 : ℕ)
    rw [hPow] at hLe
    exact (not_le_of_gt (hNorm.trans_le (min_le_right _ _))) hLe
  have hPunctured : DifferentiableOn ℂ F (Metric.ball (0 : ℂ) r \ {0}) :=
    hDiff.congr (fun z hz => if_neg (by simpa using hz.2))
  have hBall : Metric.ball (0 : ℂ) r ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds _ hr
  have hDiff0 : DifferentiableAt ℂ F 0 :=
    ((Complex.differentiableOn_compl_singleton_and_continuousAt_iff hBall).mp
      ⟨hPunctured, hContinuous⟩).differentiableAt hBall
  have hDerivative : HasDerivAt (fun z : ℂ => F z ^ (24 : ℕ)) 0 0 := by
    simpa [hF0] using hDiff0.hasDerivAt.fun_pow 24
  have hLocal : (id : ℂ → ℂ) =ᶠ[𝓝 (0 : ℂ)] (fun z => F z ^ (24 : ℕ)) := by
    filter_upwards [hBall] with z hz using (hEq z hz).symm
  exact zero_ne_one ((hDerivative.congr_of_eventuallyEq hLocal).unique (hasDerivAt_id (0 : ℂ)))

theorem exterior_at_zero : exterior 0 = 1 := by
  unfold exterior
  rw [tsum_eq_single 0 (fun n hn => by simp [exteriorTerm, zero_pow hn])]
  simp [exteriorTerm, pochhammer]

theorem no_single_valued_holomorphic_normalization {G : ℂ → ℂ}
    (hDiff : DifferentiableOn ℂ G (Metric.ball (0 : ℂ) 1 \ {0}))
    (hValue : ∀ q ∈ Metric.ball (0 : ℂ) 1 \ {0},
      ∃ w : ℂ, w ^ (24 : ℕ) = q ∧ G q = w * standard q⁻¹) : False := by
  have hOneBall : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds _ zero_lt_one
  have hCont := (exterior_differentiableOn_unit_disk.differentiableAt hOneBall).continuousAt
  have hNear : {q : ℂ | exterior q ≠ 0} ∈ 𝓝 (0 : ℂ) := by
    have hMem : exterior 0 ∈ {z : ℂ | z ≠ 0} := by simp [exterior_at_zero]
    exact hCont (isOpen_ne.mem_nhds hMem)
  obtain ⟨r, hr, hNZ⟩ := Metric.mem_nhds_iff.mp hNear
  let t := min r 1
  have ht : 0 < t := lt_min hr zero_lt_one
  have hSmall : Metric.ball (0 : ℂ) t ⊆ Metric.ball (0 : ℂ) 1 :=
    Metric.ball_subset_ball (min_le_right r 1)
  have hSub : Metric.ball (0 : ℂ) t \ {0} ⊆ Metric.ball (0 : ℂ) 1 \ {0} :=
    fun _ h => ⟨hSmall h.1, h.2⟩
  have hDen (q : ℂ) (hq : q ∈ Metric.ball (0 : ℂ) t \ {0}) : exterior q ≠ 0 :=
    hNZ (Metric.ball_subset_ball (min_le_left r 1) hq.1)
  let b : ℂ → ℂ := fun q => G q / exterior q
  have hB : DifferentiableOn ℂ b (Metric.ball (0 : ℂ) t \ {0}) :=
    (hDiff.mono hSub).div (exterior_differentiableOn_unit_disk.mono (fun _ h => hSmall h.1)) hDen
  refine no_holomorphic_root_on_punctured_disk ht hB ?_
  intro q hq
  obtain ⟨w, hw, hG⟩ := hValue q (hSub hq)
  have hq0 : q ≠ 0 := by simpa using hq.2
  have hq1 : ‖q‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hSmall hq.1
  have hb : b q = w := (div_eq_iff (hDen q hq)).mpr
    (hG.trans (congrArg (w * ·) (standard_inv_eq_exterior hq0 hq1)))
  rw [hb, hw]

end
end ManuscriptAudit.Paper8ExteriorBranchObstruction

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ExteriorBranchObstruction.no_holomorphic_root_on_punctured_disk,
      ``ManuscriptAudit.Paper8ExteriorBranchObstruction.exterior_at_zero,
      ``ManuscriptAudit.Paper8ExteriorBranchObstruction.no_single_valued_holomorphic_normalization] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
