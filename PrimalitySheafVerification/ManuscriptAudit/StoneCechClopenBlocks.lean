import Lean.Util.CollectAxioms
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Separation.Profinite

/-! A continuous discrete Čech cocycle is zero on the overlap of
sufficiently small clopen blocks of a compact Stone source. -/

namespace ManuscriptAudit.StoneCechClopenBlocks

open Set Topology Filter

noncomputable section

variable {Y X D : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    [TotallyDisconnectedSpace Y] [TopologicalSpace D] [DiscreteTopology D] [Zero D]

/-- The actual topological fibre-pair space has the induced product topology. -/
abbrev PairOver (p : Y → X) := {t : Y × Y // p t.1 = p t.2}

variable (p : Y → X) (c : C(PairOver p, D))
variable (hDiag : ∀ y, c ⟨(y,y), rfl⟩ = 0)

include hDiag in
private theorem clopenBlock (y : Y) :
    ∃ A : Set Y, IsClopen A ∧ y ∈ A ∧
      ∀ u v (e : p u = p v), u ∈ A → v ∈ A → c ⟨(u,v),e⟩ = 0 := by
  let Z : Set (PairOver p) := c ⁻¹' {0}
  have hZ : IsOpen Z := (isOpen_discrete _).preimage c.continuous
  obtain ⟨U, hU, hEq⟩ := isOpen_induced_iff.mp hZ
  have hmem : (y,y) ∈ U := by
    have h : (⟨(y,y), rfl⟩ : PairOver p) ∈ Z := hDiag y
    rw [← hEq] at h
    exact h
  have hN : U ∈ 𝓝 (y,y) := hU.mem_nhds hmem
  rw [nhds_prod_eq] at hN
  obtain ⟨A, hA, B, hB, hAB⟩ := Filter.mem_prod_iff.mp hN
  obtain ⟨V, hV, hy, hVAB⟩ :=
    isTopologicalBasis_isClopen.mem_nhds_iff.mp (Filter.inter_mem hA hB)
  refine ⟨V, hV, hy, fun u v e hu hv ↦ ?_⟩
  have h : (u,v) ∈ U := hAB ⟨(hVAB hu).1, (hVAB hv).2⟩
  have he : (⟨(u,v),e⟩ : PairOver p) ∈ Subtype.val ⁻¹' U := h
  rw [hEq] at he
  exact he

include hDiag in
/-- Finitely many literal clopen blocks cover the source and annihilate
its same-block cocycle. -/
theorem exists_blocks :
    ∃ (T : Finset Y) (V : Y → Set Y),
      (∀ i, IsClopen (V i)) ∧
      (∀ y, ∃ i ∈ T, y ∈ V i) ∧
      ∀ i u v (e : p u = p v), u ∈ V i → v ∈ V i → c ⟨(u,v),e⟩ = 0 := by
  classical
  choose V hV hmem hZero using clopenBlock p c hDiag
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover V
    (fun i ↦ (hV i).isOpen) (fun y _ ↦ Set.mem_iUnion.mpr ⟨y,hmem y⟩)
  refine ⟨T, V, hV, fun y ↦ ?_, hZero⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hT (Set.mem_univ y))
  obtain ⟨hiT, hy⟩ := Set.mem_iUnion.mp hi
  exact ⟨i, hiT, hy⟩

end
end ManuscriptAudit.StoneCechClopenBlocks

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.StoneCechClopenBlocks.exists_blocks
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
