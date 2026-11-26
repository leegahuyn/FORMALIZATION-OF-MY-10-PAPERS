import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Sites.AffineEtale

/-!
# Finite affine étale subcovers

Covering families on the small affine étale site have finite
subfamilies that are still covering. The native site criterion gives
a cover by open images of étale morphisms, and the target is affine.
-/

namespace ManuscriptAudit.AffineEtaleFiniteCover

open AlgebraicGeometry CategoryTheory Opposite

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- A covering family of actual affine étale objects has a finite covering subfamily. -/
theorem finiteSubcover_ofArrows {S : Scheme.{u}} {U : S.AffineEtale} {I : Type*}
    (V : I → S.AffineEtale) (f : ∀ i, V i ⟶ U)
    (h : Sieve.ofArrows V f ∈ Scheme.AffineEtale.topology S U) :
    ∃ t : Finset I, Sieve.ofArrows (fun i : t ↦ V i.val) (fun i : t ↦ f i.val) ∈
      Scheme.AffineEtale.topology S U := by
  classical
  let F := Scheme.AffineEtale.Spec S
  have hF : (Sieve.ofArrows V f).functorPushforward F ∈ S.smallEtaleTopology (F.obj U) :=
    (F.functorPushforward_mem_iff (Scheme.AffineEtale.topology S) S.smallEtaleTopology).2 h
  rw [Sieve.functorPushforward_ofArrows, Scheme.ofArrows_mem_smallEtaleTopology_iff] at hF
  let T := (F.obj U).left
  let R (i : I) : Set T := Set.range (F.map (f i)).left
  letI : CompactSpace T := by
    change CompactSpace (Spec (unop U.left))
    infer_instance
  have hOpen (i : I) : IsOpen (R i) := (F.map (f i)).left.isOpenMap.isOpen_range
  have hAll : (Set.univ : Set T) ⊆ ⋃ i, R i := (le_of_eq hF.symm)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover R hOpen hAll
  have hCover : (⋃ i : t, R i.val) = (Set.univ : Set T) := by
    apply Set.eq_univ_iff_forall.mpr
    intro x
    obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hx⟩
  refine ⟨t, (F.functorPushforward_mem_iff (Scheme.AffineEtale.topology S)
    S.smallEtaleTopology).1 ?_⟩
  rw [Sieve.functorPushforward_ofArrows, Scheme.ofArrows_mem_smallEtaleTopology_iff]
  exact hCover

end

end ManuscriptAudit.AffineEtaleFiniteCover

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.AffineEtaleFiniteCover.finiteSubcover_ofArrows
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
