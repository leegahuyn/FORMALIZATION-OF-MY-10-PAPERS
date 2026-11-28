import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Topology.Connected.Clopen
import PrimalitySheafVerification.ManuscriptAudit.ArithmeticLineModel

/-! Paper 2, physical p. 41: a smooth curve can have a disconnected
dual graph. The components here are the actual irreducible components
of a coproduct of two smooth affine lines. -/

namespace ManuscriptAudit.Paper2SmoothDisconnectedGraph

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ArithmeticLineModel (lineMap line_smooth)

noncomputable section

variable (K : Type) [Field K]

abbrev line := Spec (CommRingCat.of (Polynomial K))
abbrev twoLines : Scheme := line K ⨿ line K

/-- The genuine smooth curve over the given field. -/
def structureMap : twoLines K ⟶ Spec (CommRingCat.of K) :=
  coprod.desc (lineMap K) (lineMap K)

theorem structureMap_smooth : Smooth (structureMap K) := by
  refine (IsZariskiLocalAtSource.iff_of_openCover (P := @Smooth)
    (f := structureMap K) (coprodOpenCover.{0} (line K) (line K))).mpr ?_
  intro j
  rcases j with j | j
  · change Smooth (coprod.inl ≫ structureMap K)
    rw [structureMap, coprod.inl_desc]
    exact line_smooth K
  · change Smooth (coprod.inr ≫ structureMap K)
    rw [structureMap, coprod.inr_desc]
    exact line_smooth K

abbrev inclusion (a : Bool) : line K ⟶ twoLines K :=
  if a then coprod.inr else coprod.inl

def piece (a : Bool) : Set (twoLines K) := Set.range (inclusion K a)

private theorem piece_open (a : Bool) : IsOpen (piece K a) := by
  cases a
  · exact (coprod.inl : line K ⟶ twoLines K).isOpenEmbedding.isOpen_range
  · exact (coprod.inr : line K ⟶ twoLines K).isOpenEmbedding.isOpen_range

private theorem piece_compl : IsCompl (piece K false) (piece K true) :=
  isCompl_range_inl_inr (line K) (line K)

private theorem piece_clopen (a : Bool) : IsClopen (piece K a) := by
  refine ⟨?_, piece_open K a⟩
  cases a
  · rw [← isOpen_compl_iff, (piece_compl K).compl_eq]
    exact piece_open K true
  · rw [← isOpen_compl_iff, (piece_compl K).symm.compl_eq]
    exact piece_open K false

private theorem piece_irreducible (a : Bool) : IsIrreducible (piece K a) := by
  letI : IrreducibleSpace (line K) :=
    inferInstanceAs (IrreducibleSpace (PrimeSpectrum (Polynomial K)))
  simpa only [piece, Set.image_univ] using
    (IrreducibleSpace.isIrreducible_univ (line K)).image (inclusion K a)
      (inclusion K a).continuous.continuousOn

private theorem pieces_cover (x : twoLines K) : ∃ a : Bool, x ∈ piece K a := by
  obtain ⟨x, rfl⟩ := (coprodMk (line K) (line K)).surjective x
  rcases x with x | x
  · exact ⟨false, x, (coprodMk_inl (line K) (line K) x).symm⟩
  · exact ⟨true, x, (coprodMk_inr (line K) (line K) x).symm⟩

private theorem piece_component (a : Bool) : piece K a ∈ irreducibleComponents (twoLines K) := by
  refine ⟨piece_irreducible K a, fun S hS hSub ↦ ?_⟩
  obtain ⟨x, hx⟩ := (piece_irreducible K a).nonempty
  exact hS.isPreirreducible.isPreconnected.subset_isClopen (piece_clopen K a) ⟨x, hSub hx, hx⟩

/-- The actual irreducible components are precisely the two indicated affine lines. -/
theorem irreducibleComponents_eq_range :
    irreducibleComponents (twoLines K) = Set.range (piece K) := by
  ext S
  constructor
  · intro hS
    obtain ⟨x, hx⟩ := hS.1.nonempty
    obtain ⟨a, ha⟩ := pieces_cover K x
    have hSub := hS.1.isPreirreducible.isPreconnected.subset_isClopen
      (piece_clopen K a) ⟨x, hx, ha⟩
    exact ⟨a, Set.Subset.antisymm (hS.2 (piece_irreducible K a) hSub) hSub⟩
  · rintro ⟨a, rfl⟩
    exact piece_component K a

theorem pieces_distinct : piece K false ≠ piece K true := by
  intro h
  obtain ⟨x, hx⟩ := (piece_irreducible K false).nonempty
  exact Set.disjoint_left.mp (piece_compl K).disjoint hx (h ▸ hx)

/-- Vertices are the two actual components, adjacent if their subsets meet. -/
def dualGraph : SimpleGraph Bool where
  Adj a b := a ≠ b ∧ ((piece K a) ∩ (piece K b)).Nonempty
  symm.symm a b h := ⟨h.1.symm, Set.inter_comm _ _ ▸ h.2⟩
  loopless.irrefl a h := h.1 rfl

theorem dualGraph_empty : dualGraph K = ⊥ := by
  ext a b
  constructor
  · rintro ⟨hne, x, hx1, hx2⟩
    cases a <;> cases b
    · exact (hne rfl).elim
    · exact (Set.disjoint_left.mp (piece_compl K).disjoint hx1 hx2).elim
    · exact (Set.disjoint_left.mp (piece_compl K).symm.disjoint hx1 hx2).elim
    · exact (hne rfl).elim
  · intro h
    exact False.elim h

theorem smooth_dualGraph_not_tree : Smooth (structureMap K) ∧ ¬ (dualGraph K).IsTree := by
  refine ⟨structureMap_smooth K, ?_⟩
  rw [dualGraph_empty]
  exact fun h ↦ SimpleGraph.not_connected_bot h.connected

end
end ManuscriptAudit.Paper2SmoothDisconnectedGraph

open Lean Elab Command in
run_cmd do
  for name in [``ManuscriptAudit.Paper2SmoothDisconnectedGraph.structureMap_smooth,
      ``ManuscriptAudit.Paper2SmoothDisconnectedGraph.irreducibleComponents_eq_range,
      ``ManuscriptAudit.Paper2SmoothDisconnectedGraph.pieces_distinct,
      ``ManuscriptAudit.Paper2SmoothDisconnectedGraph.dualGraph_empty,
      ``ManuscriptAudit.Paper2SmoothDisconnectedGraph.smooth_dualGraph_not_tree] do
    let ax ← collectAxioms name
    let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
