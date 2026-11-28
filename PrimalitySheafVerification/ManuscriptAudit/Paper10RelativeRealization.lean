import Lean.Util.CollectAxioms
import Mathlib.Tactic.Linarith
import PrimalitySheafVerification.ManuscriptAudit.RealFormInnerProduct
import PrimalitySheafVerification.ManuscriptAudit.Paper10RelativeBilinearForm
import PrimalitySheafVerification.ManuscriptAudit.Paper10FriedrichsFormRepresentation

/-! A real form satisfying the relative bound has a native self-adjoint
realization with the same form domain and the quantitative lower bound. -/

namespace ManuscriptAudit.Paper10RelativeRealization

open Paper10RelativeBilinearForm Paper10FriedrichsResolvent
open Paper10FriedrichsShift Paper10FriedrichsFormRepresentation
open scoped RealInnerProductSpace

noncomputable section

variable {D H : Type*} [AddCommGroup D] [Module ℝ D]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The form's real-valued relative bound constructs an actual self-adjoint operator. -/
theorem exists_selfAdjoint (ι : D →ₗ[ℝ] H) (hι : Function.Injective ι) (hDense : DenseRange ι)
    (Q V : D →ₗ[ℝ] D →ₗ[ℝ] ℝ) (hQ : ∀ u w, Q w u = Q u w)
    (hV : ∀ u w, V w u = V u w)
    (m a b : ℝ) (hm : 0 ≤ m) (ha₀ : 0 ≤ a) (ha : a < 1) (hb : 0 ≤ b)
    (hLower : ∀ u, -m * ‖ι u‖ ^ 2 ≤ Q u u)
    (hPerturb : ∀ u, |V u u| ≤ a * Q u u + b * ‖ι u‖ ^ 2)
    (hComplete : letI := (originalCore ι hι Q hQ m hLower).toNormedAddCommGroup
      CompleteSpace D) :
    ∃ T : H →ₗ.[ℝ] H, IsSelfAdjoint T ∧
      (∀ x y, (x,y) ∈ T.graph ↔ ∃ u : D, ι u = x ∧
        ∀ w : D, ⟪y,ι w⟫ = Q u w + V u w) ∧
      (∀ x y, (x,y) ∈ T.graph → -((1-a)*m+b) * ‖x‖ ^ 2 ≤ ⟪y,x⟫) := by
  let c := (1-a)*(m+1)+b
  let P := perturbedCore ι hι Q V hQ hV m a b hm ha₀ ha hb hLower hPerturb
  letI := P.toNormedAddCommGroup
  letI : InnerProductSpace ℝ D := RealFormInnerProduct.innerProductSpace P
  letI : CompleteSpace D := complete_perturbed ι hι Q V hQ hV m a b hm ha₀ ha hb
    hLower hPerturb hComplete
  have hForm (u w : D) : ⟪u,w⟫ = Q u w + V u w + c * ⟪ι u,ι w⟫ := by
    change (Q+V) u w + c * ⟪ι u,ι w⟫ = _
    rw [LinearMap.add_apply, LinearMap.add_apply]
  have hNorm (u : D) : ‖u‖^2 = Q u u + V u u + c * ‖ι u‖^2 := by
    calc
      _ = ⟪u,u⟫ := (real_inner_self_eq_norm_sq u).symm
      _ = _ := by rw [hForm, real_inner_self_eq_norm_sq]
  have hN (u : D) : (1-a) * ‖ι u‖^2 ≤ ‖u‖^2 := by
    have h₁ : ‖ι u‖^2 ≤ Q u u + (m+1)*‖ι u‖^2 := by nlinarith only [hLower u]
    have h₂ := (Paper10RelativeFormBounds.shifted_comparison
      (fun u => Q u u) (fun u => V u u) (fun u => ‖ι u‖^2) m a b hm ha₀ hb
      (fun u => sq_nonneg _) hLower hPerturb u).1
    rw [hNorm]
    exact (mul_le_mul_of_nonneg_left h₁ (sub_nonneg.mpr ha.le)).trans h₂
  let s := Real.sqrt (1-a)
  have hs : 0 < s := Real.sqrt_pos.mpr (sub_pos.mpr ha)
  let J : D →L[ℝ] H := ι.mkContinuous (1/s) (fun u => by
    have hs' : (s * ‖ι u‖)^2 ≤ ‖u‖^2 := by
      rw [mul_pow, show s^2 = 1-a from Real.sq_sqrt (sub_nonneg.mpr ha.le)]
      exact hN u
    have hd := (sq_le_sq₀ (mul_nonneg hs.le (norm_nonneg _)) (norm_nonneg _)).mp hs'
    have h := (le_div_iff₀ hs).mpr (by simpa only [mul_comm] using hd)
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using h)
  have hJ : DenseRange J := hDense
  refine ⟨unshifted J c, unshifted_selfAdjoint J c hJ, ?_, ?_⟩
  · intro x y
    rw [unshifted_graph_iff, realization_form_iff J hJ]
    change (∃ u : D, ι u = x ∧ ∀ w, ⟪u,w⟫ = ⟪y+c • x,ι w⟫) ↔ _
    constructor
    · rintro ⟨u, hu, h⟩
      refine ⟨u, hu, fun w => ?_⟩
      have he := h w
      rw [hForm, inner_add_left, real_inner_smul_left, ← hu] at he
      linarith only [he]
    · rintro ⟨u, hu, h⟩
      refine ⟨u, hu, fun w => ?_⟩
      rw [hForm, inner_add_left, real_inner_smul_left, ← hu, h w]
  · intro x y hxy
    exact graph_lower_bound J hJ c (fun u => Q u u) (fun u => V u u)
      hNorm m a b ha hLower hPerturb hxy

end
end ManuscriptAudit.Paper10RelativeRealization

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper10RelativeRealization.exists_selfAdjoint
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
