import Lean.Util.CollectAxioms
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Separation.Profinite

/-! A discrete finite-valued continuous section on a closed subspace
of a Stone space extends to the whole space. -/

namespace ManuscriptAudit.StoneFiniteSectionExtension

open Set Topology

noncomputable section

variable {X D : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] [TopologicalSpace D] [DiscreteTopology D]
    [Finite D] [Nonempty D]

/-- The genuine extension uses a disjoint clopen partition enclosing
the finitely many closed fibers in the ambient compact space. -/
theorem exists_extension (Z : Set X) (hZ : IsClosed Z) (s : C(Z, D)) :
    ∃ f : C(X, D), ∀ x : Z, f x = s x := by
  classical
  let E (d : D) : Set X := (Subtype.val : Z → X) '' (s ⁻¹' {d})
  have hE (d : D) : IsClosed (E d) :=
    hZ.isClosedEmbedding_subtypeVal.isClosedMap _ (isClosed_singleton.preimage s.continuous)
  have hDis : (univ : Set D).PairwiseDisjoint E := by
    intro i _ j _ hij
    refine Set.disjoint_left.mpr ?_
    rintro x ⟨u, hu, rfl⟩ ⟨v, hv, hev⟩
    have hEq : v = u := Subtype.ext hev
    have hu' : s u = i := Set.mem_singleton_iff.mp hu
    have hv' : s v = j := Set.mem_singleton_iff.mp hv
    exact hij (hu'.symm.trans ((congrArg s hEq).symm.trans hv'))
  obtain ⟨C, hC, hSub, _, hCover, hCD⟩ :=
    exists_clopen_partition_of_clopen_cover (Z := E) (D := fun _ : D ↦ (univ : Set X))
      hE (fun _ ↦ isClopen_univ) (fun _ ↦ subset_univ _) hDis
  have hExists (x : X) : ∃ d, x ∈ C d :=
    Set.mem_iUnion.mp <| hCover (Set.mem_iUnion.mpr ⟨Classical.arbitrary D, Set.mem_univ x⟩)
  choose f hf using hExists
  have hUnique (x : X) {d e : D} (hd : x ∈ C d) (he : x ∈ C e) : d = e := by
    by_contra hn
    exact Set.disjoint_left.mp (hCD (Set.mem_univ _) (Set.mem_univ _) hn) hd he
  have hCont : Continuous f := by
    apply continuous_def.mpr
    intro U _
    have hEq : f ⁻¹' U = ⋃ d ∈ U, C d := by
      ext x
      constructor
      · intro hx
        exact Set.mem_iUnion.mpr ⟨f x, Set.mem_iUnion.mpr ⟨hx, hf x⟩⟩
      · intro hx
        obtain ⟨d, hd⟩ := Set.mem_iUnion.mp hx
        obtain ⟨hdU, hdC⟩ := Set.mem_iUnion.mp hd
        change f x ∈ U
        rw [hUnique x (hf x) hdC]
        exact hdU
    rw [hEq]
    exact isOpen_biUnion (fun d _ ↦ (hC d).isOpen)
  refine ⟨⟨f, hCont⟩, fun x ↦ hUnique x (hf x) ?_⟩
  exact hSub (s x) ⟨x, Set.mem_singleton _, rfl⟩

end
end ManuscriptAudit.StoneFiniteSectionExtension

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.StoneFiniteSectionExtension.exists_extension
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
