import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.CommAlgCat.Basic
import PrimalitySheafVerification.ManuscriptAudit.FinitePrincipalCoverAlgebra

/-! A discrete section on a closed subspace of an affine spectrum lifts
on one genuine affine faithfully flat étale cover. -/

namespace ManuscriptAudit.FinitePrincipalClosedSectionLift

open AlgebraicGeometry CategoryTheory Topology
open FinitePrincipalCoverAlgebra (coverMap Ring from_branch coverMap_branch_mem etale faithfullyFlat labels labels_branch)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R]
variable {Y : Type} [TopologicalSpace Y] (g : Y → PrimeSpectrum R) (hg : IsClosedEmbedding g)
variable {D : Type} [TopologicalSpace D] [DiscreteTopology D] [Nonempty D] (f : C(Y, D))

include hg in
private theorem local_basic (x : PrimeSpectrum R) :
    ∃ r : R, ∃ a : D, x ∈ (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) ∧
      ∀ y, g y ∈ (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) → a = f y := by
  have hBasis := PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)
  by_cases hx : x ∈ Set.range g
  · obtain ⟨y, rfl⟩ := hx
    have hFiber : IsOpen (f ⁻¹' {f y}) := (isOpen_discrete _).preimage f.continuous
    obtain ⟨W, hW, hPre⟩ := hg.isEmbedding.isInducing.isOpen_iff.mp hFiber
    have hY : g y ∈ W := by
      change y ∈ g ⁻¹' W
      rw [hPre]
      rfl
    obtain ⟨_, ⟨r, rfl⟩, hr, hs⟩ := hBasis.isOpen_iff.mp hW (g y) hY
    refine ⟨r, f y, hr, fun z hz ↦ ?_⟩
    have h : z ∈ g ⁻¹' W := hs hz
    rw [hPre] at h
    change f z = f y at h
    exact h.symm
  · obtain ⟨_, ⟨r, rfl⟩, hr, hs⟩ := hBasis.isOpen_iff.mp hg.isClosed_range.isOpen_compl x hx
    refine ⟨r, Classical.choice ‹Nonempty D›, hr, fun y hy ↦ ?_⟩
    exact ((hs hy) ⟨y, rfl⟩).elim

include hg in
set_option maxHeartbeats 1500000 in
/-- Local constants coalesce into an actual continuous lift on the
product of a finite principal-open refinement. -/
theorem exists_cover_lift :
    ∃ B : CommAlgCat.{0} R, Module.FaithfullyFlat R B ∧ Algebra.Etale R B ∧
      ∃ t : C(Spec (CommRingCat.of B), D),
        ∀ (p : PrimeSpectrum B) (y : Y), PrimeSpectrum.comap (algebraMap R B) p = g y → t p = f y := by
  classical
  choose r a hr ha using fun x ↦ local_basic g hg f x
  let W (x : PrimeSpectrum R) := (PrimeSpectrum.basicOpen (r x) : Set (PrimeSpectrum R))
  have hCover : (Set.univ : Set (PrimeSpectrum R)) ⊆ ⋃ x, W x :=
    fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hr x⟩
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover W
    (fun x ↦ PrimeSpectrum.isOpen_basicOpen) hCover
  let I := ↥S
  let r' : I → R := fun i ↦ r i.val
  let a' : I → D := fun i ↦ a i.val
  have hRef (p : PrimeSpectrum R) : ∃ i : I, p ∈ (PrimeSpectrum.basicOpen (r' i) : Set (PrimeSpectrum R)) := by
    obtain ⟨x, hx, hp⟩ := Set.mem_iUnion₂.mp (hS (Set.mem_univ p))
    exact ⟨⟨x, hx⟩, hp⟩
  refine ⟨CommAlgCat.of R (Ring r'), faithfullyFlat r' hRef, etale r', labels r' a', ?_⟩
  intro p y h
  obtain ⟨i, q, rfl⟩ := from_branch r' p
  rw [labels_branch]
  apply ha i.val y
  rw [← h]
  exact coverMap_branch_mem r' i q

end

end ManuscriptAudit.FinitePrincipalClosedSectionLift

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.FinitePrincipalClosedSectionLift.exists_cover_lift
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
