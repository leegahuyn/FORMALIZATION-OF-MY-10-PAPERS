import Lean.Util.CollectAxioms
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-! Nonzero eigenvalues of a compact self-adjoint operator are isolated quantitatively. -/

namespace ManuscriptAudit.Paper8CompactEigenvalueIsolation

open Filter Set Module.End
open scoped InnerProductSpace Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem finite_of_separated_map_into_compact {I : Type*} (K : Set H) (hK : IsCompact K)
    (f : I → H) (hf : ∀ i, f i ∈ K) {ε : ℝ} (hε : 0 < ε)
    (hSep : ∀ i j, i ≠ j → ε ≤ dist (f i) (f j)) : Finite I := by
  classical
  obtain ⟨s, hs, hCover⟩ := Metric.totallyBounded_iff.1 hK.totallyBounded (ε / 3) (by positivity)
  have hHit (i : I) : ∃ y ∈ s, dist (f i) y < ε / 3 := by
    obtain ⟨y, hy⟩ := Set.mem_iUnion.mp (hCover (hf i))
    obtain ⟨hyS, hBall⟩ := Set.mem_iUnion.mp hy
    exact ⟨y, hyS, Metric.mem_ball.mp hBall⟩
  choose y hy hyⱼ using hHit
  haveI : Finite s := hs
  refine Finite.of_injective (fun i : I => (⟨y i, hy i⟩ : s)) ?_
  intro i j hEq
  by_contra hij
  have hDist : dist (y i) (f j) < ε / 3 := by
    rw [show y i = y j from congrArg Subtype.val hEq, dist_comm]
    exact hyⱼ j
  linarith [dist_triangle (f i) (y i) (f j), hyⱼ i, hDist, hSep i j hij]

private theorem exists_unit_eigenvector (T : H →L[ℂ] H) (μ : Eigenvalues T.toLinearMap) :
    ∃ v : H, v ∈ eigenspace T.toLinearMap (μ : ℂ) ∧ ‖v‖ = 1 := by
  have hμ : HasEigenvalue T.toLinearMap (μ : ℂ) := μ.2
  obtain ⟨v, hv, hV⟩ := hμ.exists_hasEigenvector
  let w := (((‖v‖⁻¹ : ℝ) : ℂ) • v)
  refine ⟨w, Submodule.smul_mem _ _ hv, ?_⟩
  unfold w
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hV)]

theorem finite_compact_eigenvalues_outside_ball (T : H →L[ℂ] H)
    (hT : IsCompactOperator T) (hS : T.IsSymmetric) {ε : ℝ} (hε : 0 < ε) :
    {μ : Eigenvalues T.toLinearMap | ε ≤ ‖(μ : ℂ)‖}.Finite := by
  let I := {μ : Eigenvalues T.toLinearMap // ε ≤ ‖(μ : ℂ)‖}
  have hExists (i : I) : ∃ v : H, v ∈ eigenspace T.toLinearMap (i.1 : ℂ) ∧ ‖v‖ = 1 :=
    exists_unit_eigenvector T i.1
  choose v hv hNorm using hExists
  obtain ⟨K, hK, hTIn⟩ := hT.image_closedBall_subset_compact 1
  have hIn (i : I) : T (v i) ∈ K := by
    apply hTIn
    refine ⟨v i, ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, hNorm i] <;> exact le_rfl
  have hTVal (i : I) : T (v i) = (i.1 : ℂ) • v i := mem_eigenspace_iff.mp (hv i)
  have hTVec (i : I) : T (v i) ∈ eigenspace T.toLinearMap (i.1 : ℂ) := by
    rw [hTVal]
    exact Submodule.smul_mem _ _ (hv i)
  have hTNorm (i : I) : ‖T (v i)‖ = ‖(i.1 : ℂ)‖ := by
    rw [hTVal, norm_smul, hNorm, mul_one]
  have hSep (i j : I) (hij : i ≠ j) : ε ≤ dist (T (v i)) (T (v j)) := by
    have hNe : (i.1 : ℂ) ≠ j.1 := fun h => hij (Subtype.ext (Subtype.ext h))
    have hS' : T.toLinearMap.IsSymmetric := hS
    have hOrtho : ⟪T (v i), T (v j)⟫_ℂ = 0 :=
      hS'.orthogonalFamily_eigenspaces hNe ⟨_, hTVec i⟩ ⟨_, hTVec j⟩
    have hEq : ‖T (v i) - T (v j)‖ ^ 2 = ‖T (v i)‖ ^ 2 + ‖T (v j)‖ ^ 2 := by
      rw [norm_sub_sq (𝕜 := ℂ), hOrtho] <;> norm_num
    have hLe : ε ≤ ‖T (v i)‖ := by rw [hTNorm]; exact i.2
    have hSq : ε ^ 2 ≤ ‖T (v i) - T (v j)‖ ^ 2 := by
      rw [hEq]
      exact (pow_le_pow_left₀ hε.le hLe 2).trans (le_add_of_nonneg_right (sq_nonneg _))
    rw [dist_eq_norm]
    simpa only [abs_of_nonneg hε.le, abs_of_nonneg (norm_nonneg _)] using sq_le_sq.mp hSq
  exact finite_of_separated_map_into_compact K hK (fun i : I => T (v i)) hIn hε hSep

theorem compact_eigenvalue_isolated (T : H →L[ℂ] H) (hT : IsCompactOperator T)
    (hS : T.IsSymmetric) (μ : Eigenvalues T.toLinearMap) (hμ : (μ : ℂ) ≠ 0) :
    ∃ r > (0 : ℝ), ∀ ν : Eigenvalues T.toLinearMap, ν ≠ μ → r ≤ ‖(ν : ℂ) - (μ : ℂ)‖ := by
  let ε := ‖(μ : ℂ)‖ / 2
  have hε : 0 < ε := half_pos (norm_pos_iff.mpr hμ)
  let A : Set (Eigenvalues T.toLinearMap) := {ν | ε ≤ ‖(ν : ℂ)‖}
  have hf : A.Finite := finite_compact_eigenvalues_outside_ball T hT hS hε
  let B : Set ℂ := Subtype.val '' (A \ {μ})
  have hDiff : (A \ {μ}).Finite := hf.diff
  have hB : B.Finite := hDiff.image Subtype.val
  have hNot : (μ : ℂ) ∈ Bᶜ := by
    rintro ⟨ν, hν, hEq⟩
    exact hν.2 (Set.mem_singleton_iff.mpr (Subtype.ext hEq))
  obtain ⟨d, hd, hBall⟩ := Metric.mem_nhds_iff.1 (hB.isClosed.isOpen_compl.mem_nhds hNot)
  refine ⟨min d ε, lt_min hd hε, ?_⟩
  intro ν hNe
  by_cases hv : ε ≤ ‖(ν : ℂ)‖
  · have hOutside : d ≤ ‖(ν : ℂ) - (μ : ℂ)‖ := by
      apply le_of_not_gt
      intro hLt
      have hBallMem : (ν : ℂ) ∈ Metric.ball (μ : ℂ) d := by
        simpa only [Metric.mem_ball, dist_eq_norm] using hLt
      exact (hBall hBallMem) ⟨ν, ⟨hv, fun hm => hNe (Set.mem_singleton_iff.mp hm)⟩, rfl⟩
    exact (min_le_left _ _).trans hOutside
  · have hTri : ‖(μ : ℂ)‖ ≤ ‖(ν : ℂ)‖ + ‖(ν : ℂ) - (μ : ℂ)‖ := by
      have h := norm_sub_le (ν : ℂ) ((ν : ℂ) - (μ : ℂ))
      simpa only [sub_sub_cancel] using h
    have hSmall : ‖(ν : ℂ)‖ < ε := lt_of_not_ge hv
    have hOutside : ε ≤ ‖(ν : ℂ) - (μ : ℂ)‖ := by unfold ε at *; linarith
    exact (min_le_right _ _).trans hOutside

end
end ManuscriptAudit.Paper8CompactEigenvalueIsolation

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8CompactEigenvalueIsolation.compact_eigenvalue_isolated
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
