import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import PrimalitySheafVerification.ManuscriptAudit.SplitClosedProetaleLift
import PrimalitySheafVerification.ManuscriptAudit.ProetaleFiniteQuasiCompactCover

/-! Split closed immersions with quasi-compact open complement have
epimorphism-preserving direct image on the actual pro-étale site. -/

namespace ManuscriptAudit.SplitClosedProetaleDirectImage

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleBaseChange

noncomputable section
universe u v

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev C (X : Scheme.{u}) := Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{v}

private abbrev openObject {T : Scheme.{u}} (U : T.ProEt) (W : U.left.Opens) : T.ProEt :=
  Scheme.ProEt.mk (W.ι ≫ U.hom)

private abbrev openArrow {T : Scheme.{u}} (U : T.ProEt) (W : U.left.Opens) :
    openObject U W ⟶ U := MorphismProperty.Over.homMk W.ι rfl

variable {S T : Scheme.{u}} (i : S ⟶ T) [IsClosedImmersion i]

/-- The literal complement of the closed fiber in an actual chart. -/
def complement (U : T.ProEt) : U.left.Opens :=
  ⟨(Set.range (pullback.fst U.hom i))ᶜ,
    (pullback.fst U.hom i).isClosedEmbedding.isClosed_range.isOpen_compl⟩

private theorem off_empty (U : T.ProEt) :
    IsEmpty ((baseChange i).obj (openObject U (complement i U))).left := by
  let W := complement i U
  let V := openObject U W
  let g := openArrow U W
  refine ⟨fun y ↦ ?_⟩
  have hComp : ((baseChange i).map g).left ≫ pullback.fst U.hom i =
      pullback.fst V.hom i ≫ g.left := by
    simp only [baseChange, MorphismProperty.Over.pullback_map_left, pullback.lift_fst]
  have hp := congrArg (fun f : ((baseChange i).obj V).left ⟶ U.left ↦ f y) hComp
  have hy : g.left (pullback.fst V.hom i y) ∉ Set.range (pullback.fst U.hom i) :=
    (pullback.fst V.hom i y : W).property
  exact hy ⟨((baseChange i).map g).left y, hp⟩

variable [IsAffine S]
variable (r : T ⟶ S) (hir : i ≫ r = 𝟙 S)

private theorem affine_image_cover {F G : C.{u,v} S}
    (α : F ⟶ G) [Sheaf.IsLocallySurjective α] (U : T.ProEt) [IsAffine U.left]
    (hQC : QuasiCompact (complement i U).ι)
    (s : ((directImage i AddCommGrpCat.{v}).obj G).obj.obj (op U)) :
    Presheaf.imageSieve ((directImage i AddCommGrpCat.{v}).map α).hom s ∈
      Scheme.ProEt.topology T U := by
  classical
  obtain ⟨V, g, hV, hCov, b, hb⟩ := SplitClosedProetaleLift.exists_on_support i r hir α U s
  letI : IsAffine V.left := hV
  let W := complement i U
  let R := Presheaf.imageSieve ((directImage i AddCommGrpCat.{v}).map α).hom s
  let V' (a : Bool) : T.ProEt := if a then V else openObject U W
  let f (a : Bool) : V' a ⟶ U := by
    cases a
    · exact openArrow U W
    · exact g
  have hFqc (a : Bool) : QuasiCompact (f a).left := by
    cases a
    · exact hQC
    · exact inferInstanceAs (QuasiCompact g.left)
  have hFull (x : U.left) : ∃ a, ∃ y : (V' a).left, (f a).left y = x := by
    by_cases h : x ∈ Set.range (pullback.fst U.hom i)
    · obtain ⟨y, hy⟩ := hCov h
      exact ⟨true, y, hy⟩
    · exact ⟨false, ⟨x, h⟩, rfl⟩
  have hSections (a : Bool) : R (f a) := by
    cases a
    · letI : IsEmpty ((baseChange i).obj (openObject U W)).left := off_empty i U
      letI := ProetaleAffineSingletonLift.sections_subsingleton_of_empty G
        ((baseChange i).obj (openObject U W))
      exact ⟨0, Subsingleton.elim _ _⟩
    · exact ⟨b, hb⟩
  refine (Scheme.ProEt.topology T).superset_covering ?_
    (ProetaleFiniteQuasiCompactCover.covering V' f hFqc hFull)
  intro P a ha
  obtain ⟨j, t, rfl⟩ := (Sieve.mem_ofArrows_iff V' f a).mp ha
  exact R.downward_closed (hSections j) t

/-- The native direct image is locally onto whenever the original sheaf
map is locally onto and the closed support has quasi-compact complement. -/
theorem map_locallySurjective
    (hQC : ∀ (U : T.ProEt), IsAffine U.left → QuasiCompact (complement i U).ι)
    {F G : C.{u,v} S} (α : F ⟶ G) [Sheaf.IsLocallySurjective α] :
    Sheaf.IsLocallySurjective ((directImage i AddCommGrpCat.{v}).map α) where
  imageSieve_mem {U} s := by
    apply ProetaleFiniteQuasiCompactCover.of_affine_pullbacks
    intro V hV g
    let Q := (directImage i AddCommGrpCat.{v}).obj G
    let I := (directImage i AddCommGrpCat.{v}).obj F
    let β : I ⟶ Q := (directImage i AddCommGrpCat.{v}).map α
    let t := Q.obj.map g.op s
    refine (Scheme.ProEt.topology T).superset_covering ?_
      (affine_image_cover i r hir α V (hQC V hV) t)
    intro W f hf
    obtain ⟨b, hb⟩ := hf
    refine ⟨b, ?_⟩
    change β.hom.app (op W) b = Q.obj.map (f ≫ g).op s
    rw [op_comp, Q.obj.map_comp, ConcreteCategory.comp_apply]
    exact hb

theorem map_epi
    (hQC : ∀ (U : T.ProEt), IsAffine U.left → QuasiCompact (complement i U).ι)
    {F G : C.{u,v} S} (α : F ⟶ G) [Epi α] :
    Epi ((directImage i AddCommGrpCat.{v}).map α) := by
  letI : Sheaf.IsLocallySurjective α :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{v} α).mpr inferInstance
  letI := map_locallySurjective i r hir hQC α
  exact Sheaf.epi_of_isLocallySurjective _

end
end ManuscriptAudit.SplitClosedProetaleDirectImage

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.SplitClosedProetaleDirectImage.map_epi
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{name} depends on unexpected axioms {ax}"
  logInfo m!"{name} uses {ax}"
