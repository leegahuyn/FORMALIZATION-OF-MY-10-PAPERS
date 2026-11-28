import Lean.Util.CollectAxioms
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import PrimalitySheafVerification.ManuscriptAudit.Paper10RelativeBilinearForm

/-! Compactness of the original form inclusion is preserved by the
actual relative deformation of the form norm. -/

namespace ManuscriptAudit.Paper10RelativeFormCompact

open Paper10RelativeBilinearForm
open scoped RealInnerProductSpace

noncomputable section

variable {D H : Type*} [AddCommGroup D] [Module ℝ D]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

private def coreNorm (P : InnerProductSpace.Core ℝ D) (u : D) : ℝ :=
  letI := P.toNormedAddCommGroup
  ‖u‖

private theorem coreNorm_nonneg (P : InnerProductSpace.Core ℝ D) (u : D) : 0 ≤ coreNorm P u := by
  letI := P.toNormedAddCommGroup
  exact norm_nonneg u

private theorem coreNorm_sq (P : InnerProductSpace.Core ℝ D) (u : D) :
    coreNorm P u ^ 2 = P.inner u u := by
  change Real.sqrt (P.inner u u) ^ 2 = _
  exact Real.sq_sqrt (P.re_inner_nonneg u)

/-- The genuine compact inclusion of the unperturbed form domain remains compact
when the common domain is given the shifted perturbed form norm. -/
theorem compact_perturbed
    (ι : D →ₗ[ℝ] H) (hι : Function.Injective ι)
    (Q V : D →ₗ[ℝ] D →ₗ[ℝ] ℝ)
    (hQ : ∀ u w, Q w u = Q u w) (hV : ∀ u w, V w u = V u w)
    (m a b : ℝ) (hm : 0 ≤ m) (ha₀ : 0 ≤ a) (ha : a < 1) (hb : 0 ≤ b)
    (hLower : ∀ u, -m * ‖ι u‖ ^ 2 ≤ Q u u)
    (hPerturb : ∀ u, |V u u| ≤ a * Q u u + b * ‖ι u‖ ^ 2)
    (hK : letI := (originalCore ι hι Q hQ m hLower).toNormedAddCommGroup
      IsCompactOperator (ι : D → H)) :
    letI := (perturbedCore ι hι Q V hQ hV m a b hm ha₀ ha hb hLower hPerturb).toNormedAddCommGroup
    IsCompactOperator (ι : D → H) := by
  let P := originalCore ι hι Q hQ m hLower
  let F := perturbedCore ι hι Q V hQ hV m a b hm ha₀ ha hb hLower hPerturb
  let s := Real.sqrt (1-a)
  have hs : 0 < s := Real.sqrt_pos.mpr (sub_pos.mpr ha)
  have hP (u : D) : coreNorm P u ^ 2 = Q u u + (m+1)*‖ι u‖^2 := by
    rw [coreNorm_sq]
    change Q u u + (m+1)*⟪ι u,ι u⟫ = _
    rw [real_inner_self_eq_norm_sq]
  have hF (u : D) : coreNorm F u ^ 2 =
      Q u u + V u u + ((1-a)*(m+1)+b)*‖ι u‖^2 := by
    rw [coreNorm_sq]
    change (Q + V) u u + ((1-a)*(m+1)+b)*⟪ι u,ι u⟫ = _
    rw [LinearMap.add_apply, LinearMap.add_apply, real_inner_self_eq_norm_sq]
  have hNorm (u : D) : s * coreNorm P u ≤ coreNorm F u := by
    apply (sq_le_sq₀ (mul_nonneg hs.le (coreNorm_nonneg P u)) (coreNorm_nonneg F u)).mp
    rw [mul_pow, show s^2 = 1-a from Real.sq_sqrt (sub_nonneg.mpr ha.le), hP, hF]
    exact (Paper10RelativeFormBounds.shifted_comparison (fun u => Q u u) (fun u => V u u)
      (fun u => ‖ι u‖ ^ 2) m a b hm ha₀ hb (fun _ => sq_nonneg _) hLower hPerturb u).1
  obtain ⟨K, r, hCK, hr, hSubset⟩ :
      ∃ (K : Set H) (r : ℝ), IsCompact K ∧ 0 < r ∧
        ∀ u, coreNorm P u < r → ι u ∈ K := by
    letI := P.toNormedAddCommGroup
    obtain ⟨K, hCK, hN⟩ := hK
    obtain ⟨r, hr, hrK⟩ := Metric.mem_nhds_iff.mp hN
    refine ⟨K,r,hCK,hr,fun u hu => hrK ?_⟩
    simpa only [Metric.mem_ball, dist_zero_right] using hu
  letI := F.toNormedAddCommGroup
  refine ⟨K, hCK, Metric.mem_nhds_iff.mpr ⟨s*r, mul_pos hs hr, ?_⟩⟩
  intro u hu
  apply hSubset u
  have hBound : coreNorm F u < s*r := by
    simpa only [Metric.mem_ball, dist_zero_right] using hu
  exact (mul_lt_mul_left hs).mp ((hNorm u).trans_lt hBound)

end
end ManuscriptAudit.Paper10RelativeFormCompact

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper10RelativeFormCompact.compact_perturbed
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
