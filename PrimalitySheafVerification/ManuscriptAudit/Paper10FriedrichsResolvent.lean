import Lean.Util.CollectAxioms
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-! The canonical resolvent of a closed positive form on a densely embedded
Hilbert form domain, and its actual unbounded self-adjoint realization. -/

namespace ManuscriptAudit.Paper10FriedrichsResolvent

open scoped InnerProductSpace

noncomputable section

variable {𝕜 D H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup D] [InnerProductSpace 𝕜 D] [CompleteSpace D]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

variable (J : D →L[𝕜] H)

def resolvent : H →L[𝕜] H := J.comp J.adjoint

theorem resolvent_symmetric (x y : H) :
    ⟪resolvent J x, y⟫_𝕜 = ⟪x, resolvent J y⟫_𝕜 := by
  change ⟪J (J.adjoint x), y⟫_𝕜 = ⟪x, J (J.adjoint y)⟫_𝕜
  exact (J.adjoint_inner_right (J.adjoint x) y).symm.trans
    (J.adjoint_inner_left (J.adjoint y) x)

private theorem resolvent_adjoint : (resolvent J).adjoint = resolvent J := by
  unfold resolvent
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]

theorem resolvent_ker (hJ : DenseRange J) : (resolvent J).ker = ⊥ := by
  have hDense : J.range.topologicalClosure = ⊤ := by
    apply Submodule.ext
    intro x
    change x ∈ closure (Set.range J) ↔ x ∈ (Set.univ : Set H)
    rw [hJ.closure_eq]
  rw [resolvent, ContinuousLinearMap.ker_self_comp_adjoint, ← J.orthogonal_range]
  exact Submodule.topologicalClosure_eq_top_iff.mp hDense

theorem resolvent_denseRange (hJ : DenseRange J) : DenseRange (resolvent J) := by
  have hDense : (resolvent J).range.topologicalClosure = ⊤ := by
    apply Submodule.topologicalClosure_eq_top_iff.mpr
    rw [(resolvent J).orthogonal_range, resolvent_adjoint, resolvent_ker J hJ]
  apply dense_iff_closure_eq.mpr
  exact congrArg (fun K : Submodule 𝕜 H => (K : Set H)) hDense

private def inverseGraph : Submodule 𝕜 (H × H) :=
  ((resolvent J).toLinearMap.comp (LinearMap.snd 𝕜 H H) - LinearMap.fst 𝕜 H H).ker

private theorem mem_inverseGraph (x y : H) :
    (x, y) ∈ inverseGraph J ↔ resolvent J y = x := by
  change resolvent J y - x = 0 ↔ _
  exact sub_eq_zero

/-- The domain and graph are those of the unbounded inverse of the actual bounded resolvent. -/
def realization : H →ₗ.[𝕜] H := (inverseGraph J).toLinearPMap

private theorem realization_graph (hJ : DenseRange J) :
    (realization J).graph = inverseGraph J := by
  apply Submodule.toLinearPMap_graph_eq
  rintro ⟨x, y⟩ h hzero
  have hy : resolvent J y = x := (mem_inverseGraph J x y).mp h
  have hmem : y ∈ (resolvent J).ker := hy.trans hzero
  rwa [resolvent_ker J hJ, Submodule.mem_bot] at hmem

theorem realization_graph_iff (hJ : DenseRange J) (x y : H) :
    (x, y) ∈ (realization J).graph ↔ resolvent J y = x := by
  rw [realization_graph J hJ, mem_inverseGraph]

private theorem realization_dense_domain (hJ : DenseRange J) :
    Dense ((realization J).domain : Set H) := by
  have hSet : ((realization J).domain : Set H) = Set.range (resolvent J) := by
    ext x
    change x ∈ (realization J).domain ↔ ∃ y, resolvent J y = x
    rw [LinearPMap.mem_domain_iff]
    exact exists_congr (fun y => realization_graph_iff J hJ x y)
  rw [hSet]
  exact resolvent_denseRange J hJ

/-- This is self-adjoint in the actual partially defined operator API. -/
theorem realization_selfAdjoint (hJ : DenseRange J) :
    IsSelfAdjoint (realization J) := by
  apply LinearPMap.isSelfAdjoint_def.mpr
  apply LinearPMap.eq_of_eq_graph
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint (realization_dense_domain J hJ),
    realization_graph J hJ]
  ext p
  rcases p with ⟨x, y⟩
  rw [Submodule.mem_adjoint_iff, mem_inverseGraph]
  constructor
  · intro h
    apply ext_inner_left 𝕜
    intro z
    calc
      ⟪z, resolvent J y⟫_𝕜 = ⟪resolvent J z, y⟫_𝕜 := (resolvent_symmetric J z y).symm
      _ = ⟪z, x⟫_𝕜 := (sub_eq_zero.mp (h (resolvent J z) z
        ((mem_inverseGraph J _ _).mpr rfl))).symm
  · intro h a b hab
    have hab' := (mem_inverseGraph J a b).mp hab
    change ⟪b, x⟫_𝕜 - ⟪a, y⟫_𝕜 = 0
    rw [← h, ← hab', resolvent_symmetric, sub_self]

/-- Every datum is represented by the unique variational solution selected by the adjoint. -/
theorem variational_solution (f : H) :
    ∃! u : D, ∀ v : D, ⟪u, v⟫_𝕜 = ⟪f, J v⟫_𝕜 := by
  refine ⟨J.adjoint f, fun v => J.adjoint_inner_left v f, ?_⟩
  intro u hu
  apply ext_inner_right 𝕜
  intro v
  exact (hu v).trans (J.adjoint_inner_left v f).symm

/-- The genuine graph is exactly the set of data represented by the form. -/
theorem realization_form_iff (hJ : DenseRange J) (x f : H) :
    (x, f) ∈ (realization J).graph ↔
      ∃ u : D, J u = x ∧ ∀ v : D, ⟪u, v⟫_𝕜 = ⟪f, J v⟫_𝕜 := by
  rw [realization_graph_iff J hJ]
  constructor
  · intro h
    exact ⟨J.adjoint f, h, fun v => J.adjoint_inner_left v f⟩
  · rintro ⟨u, hu, hForm⟩
    have hu' : u = J.adjoint f := by
      apply ext_inner_right 𝕜
      intro v
      exact (hForm v).trans (J.adjoint_inner_left v f).symm
    rw [hu'] at hu
    exact hu

end
end ManuscriptAudit.Paper10FriedrichsResolvent

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.Paper10FriedrichsResolvent.realization_graph_iff,
      ``ManuscriptAudit.Paper10FriedrichsResolvent.realization_selfAdjoint,
      ``ManuscriptAudit.Paper10FriedrichsResolvent.realization_form_iff,
      ``ManuscriptAudit.Paper10FriedrichsResolvent.variational_solution] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
