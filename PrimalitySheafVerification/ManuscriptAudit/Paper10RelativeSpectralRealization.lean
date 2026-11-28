import Lean.Util.CollectAxioms
import Mathlib.Tactic.Linarith
import PrimalitySheafVerification.ManuscriptAudit.Paper10RelativeFormCompact
import PrimalitySheafVerification.ManuscriptAudit.Paper10RelativeRealizationUnique
import PrimalitySheafVerification.ManuscriptAudit.Paper10FriedrichsFiniteSpectrum

/-! The relative deformation and the genuine spectral theorem combine on the
same closed form domain. -/

namespace ManuscriptAudit.Paper10RelativeSpectralRealization

open Paper10RelativeBilinearForm Paper10RelativeFormCompact
open Paper10FriedrichsResolvent Paper10FriedrichsShift
open Paper10FriedrichsEigenbasis Paper10FriedrichsFiniteSpectrum
open scoped RealInnerProductSpace

noncomputable section

variable {D H : Type*} [AddCommGroup D] [Module ℝ D]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The actual perturbed realization has an orthonormal eigenbasis, with finitely
many counted eigenvalues in every bounded energy range. -/
theorem exists_selfAdjoint_eigenbasis
    (ι : D →ₗ[ℝ] H) (hι : Function.Injective ι) (hDense : DenseRange ι)
    (Q V : D →ₗ[ℝ] D →ₗ[ℝ] ℝ) (hQ : ∀ u w, Q w u = Q u w)
    (hV : ∀ u w, V w u = V u w)
    (m a b : ℝ) (hm : 0 ≤ m) (ha₀ : 0 ≤ a) (ha : a < 1) (hb : 0 ≤ b)
    (hLower : ∀ u, -m * ‖ι u‖ ^ 2 ≤ Q u u)
    (hPerturb : ∀ u, |V u u| ≤ a * Q u u + b * ‖ι u‖ ^ 2)
    (hComplete : letI := (originalCore ι hι Q hQ m hLower).toNormedAddCommGroup
      CompleteSpace D)
    (hCompact : letI := (originalCore ι hι Q hQ m hLower).toNormedAddCommGroup
      IsCompactOperator (ι : D → H)) :
    ∃ (T : H →ₗ.[ℝ] H) (I : Type) (e : I → ℝ) (basis : HilbertBasis I ℝ H),
      IsSelfAdjoint T ∧
      (∀ x y, (x,y) ∈ T.graph ↔ ∃ u : D, ι u = x ∧
        ∀ w : D, ⟪y,ι w⟫ = Q u w + V u w) ∧
      (∀ i, (basis i,e i • basis i) ∈ T.graph) ∧
      ∀ R : ℝ, Finite {i // ‖e i‖ ≤ R} := by
  let c := (1-a)*(m+1)+b
  let P := perturbedCore ι hι Q V hQ hV m a b hm ha₀ ha hb hLower hPerturb
  letI := P.toNormedAddCommGroup
  letI : InnerProductSpace ℝ D := RealFormInnerProduct.innerProductSpace P
  letI : CompleteSpace D := complete_perturbed ι hι Q V hQ hV m a b hm ha₀ ha hb
    hLower hPerturb hComplete
  have hCP : IsCompactOperator (ι : D → H) :=
    compact_perturbed ι hι Q V hQ hV m a b hm ha₀ ha hb hLower hPerturb hCompact
  let J := ContinuousLinearMap.mkOfIsCompactOperator hCP
  have hJ : DenseRange J := hDense
  have hJK : IsCompactOperator (J : D → H) := hCP
  obtain ⟨basis, hBasis⟩ := exists_eigenbasis J hJ hJK
  refine ⟨unshifted J c, EigenIndex J, fun i => i.1-c, basis, unshifted_selfAdjoint J c hJ,
    ?_, ?_, ?_⟩
  · intro x y
    rw [unshifted_graph_iff J c x y, realization_form_iff J hJ x (y+c • x)]
    change (∃ u : D, ι u = x ∧ ∀ w, ⟪u,w⟫ = ⟪y+c • x,ι w⟫) ↔ _
    have hForm (u w : D) : ⟪u,w⟫ = Q u w + V u w + c * ⟪ι u,ι w⟫ := by
      change (Q+V) u w + c * ⟪ι u,ι w⟫ = _
      rw [LinearMap.add_apply, LinearMap.add_apply]
    constructor
    · rintro ⟨u, hu, h⟩
      refine ⟨u, hu, fun w => ?_⟩
      have he := h w
      rw [hForm, inner_add_left, real_inner_smul_left, ← hu] at he
      linarith only [he]
    · rintro ⟨u, hu, h⟩
      refine ⟨u, hu, fun w => ?_⟩
      rw [hForm, inner_add_left, real_inner_smul_left, ← hu, h w]
  · intro i
    apply (unshifted_graph_iff J c _ _).mpr
    rw [← add_smul, sub_add_cancel]
    exact hBasis i
  · intro R
    let M := max 1 (R + ‖c‖)
    have hM : 0 < M := zero_lt_one.trans_le (le_max_left _ _)
    letI := finite_bounded_basis_indices J hJ hJK basis hBasis M hM
    let f : {i : EigenIndex J // ‖i.1-c‖ ≤ R} → {i : EigenIndex J // ‖i.1‖ ≤ M} :=
      fun i => ⟨i.val, by
        calc
          ‖i.val.1‖ = ‖(i.val.1-c)+c‖ := congrArg norm (sub_add_cancel _ _).symm
          _ ≤ ‖i.val.1-c‖ + ‖c‖ := norm_add_le _ _
          _ ≤ R + ‖c‖ := add_le_add_right i.property _
          _ ≤ M := le_max_right _ _⟩
    exact Finite.of_injective f (fun i j h => Subtype.ext (congrArg Subtype.val h))

end
end ManuscriptAudit.Paper10RelativeSpectralRealization

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper10RelativeSpectralRealization.exists_selfAdjoint_eigenbasis
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
