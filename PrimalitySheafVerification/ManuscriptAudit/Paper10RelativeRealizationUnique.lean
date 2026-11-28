import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper10RelativeRealization

/-! The representing operator is unique because the form determines the literal graph. -/

namespace ManuscriptAudit.Paper10RelativeRealizationUnique

open Paper10RelativeBilinearForm Paper10RelativeRealization
open scoped RealInnerProductSpace

noncomputable section

variable {D H : Type*} [AddCommGroup D] [Module ℝ D]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def Represents (ι : D →ₗ[ℝ] H) (Q V : D →ₗ[ℝ] D →ₗ[ℝ] ℝ)
    (T : H →ₗ.[ℝ] H) : Prop :=
  ∀ x y, (x,y) ∈ T.graph ↔ ∃ u : D, ι u = x ∧
    ∀ w : D, ⟪y, ι w⟫ = Q u w + V u w

theorem eq_of_represents (ι : D →ₗ[ℝ] H) (Q V : D →ₗ[ℝ] D →ₗ[ℝ] ℝ)
    {S T : H →ₗ.[ℝ] H} (hS : Represents ι Q V S) (hT : Represents ι Q V T) :
    S = T := by
  apply LinearPMap.eq_of_eq_graph
  apply Submodule.ext
  rintro ⟨x,y⟩
  exact (hS x y).trans (hT x y).symm

theorem existsUnique_selfAdjoint (ι : D →ₗ[ℝ] H) (hι : Function.Injective ι) (hDense : DenseRange ι)
    (Q V : D →ₗ[ℝ] D →ₗ[ℝ] ℝ) (hQ : ∀ u w, Q w u = Q u w)
    (hV : ∀ u w, V w u = V u w)
    (m a b : ℝ) (hm : 0 ≤ m) (ha₀ : 0 ≤ a) (ha : a < 1) (hb : 0 ≤ b)
    (hLower : ∀ u, -m * ‖ι u‖ ^ 2 ≤ Q u u)
    (hPerturb : ∀ u, |V u u| ≤ a * Q u u + b * ‖ι u‖ ^ 2)
    (hComplete : letI := (originalCore ι hι Q hQ m hLower).toNormedAddCommGroup
      CompleteSpace D) :
    ∃! T : H →ₗ.[ℝ] H, IsSelfAdjoint T ∧ Represents ι Q V T ∧
      (∀ x y, (x,y) ∈ T.graph → -((1-a)*m+b) * ‖x‖ ^ 2 ≤ ⟪y,x⟫) := by
  obtain ⟨T, hA, hR, hB⟩ := exists_selfAdjoint ι hι hDense Q V hQ hV m a b
    hm ha₀ ha hb hLower hPerturb hComplete
  exact ⟨T, ⟨hA, hR, hB⟩, fun _ hS => eq_of_represents ι Q V hS.2.1 hR⟩

end
end ManuscriptAudit.Paper10RelativeRealizationUnique

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper10RelativeRealizationUnique.existsUnique_selfAdjoint
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
