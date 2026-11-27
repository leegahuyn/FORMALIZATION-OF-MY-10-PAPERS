import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleClosedSupportLocalConstants
import PrimalitySheafVerification.ManuscriptAudit.EtaleEpiLocalSurjectivity
import PrimalitySheafVerification.ManuscriptAudit.SplitClosedEtaleRefinement

/-! Direct image along a split closed immersion is exact on étale abelian sheaves. -/

namespace ManuscriptAudit.SplitClosedEtaleDirectImage

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open SmallEtaleBaseChange EtaleClosedSupportLocalConstants
open EtaleEpiLocalSurjectivity SplitClosedEtaleRefinement

noncomputable section
universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{u}

private theorem cover_iff_points {T : Scheme.{u}} {U : T.Etale} (R : Sieve U) :
    R ∈ T.smallEtaleTopology U ↔
      ∀ x : U.left, ∃ (V : T.Etale) (g : V ⟶ U), R g ∧ x ∈ Set.range g.left := by
  constructor
  · intro h x
    rw [← Sieve.ofArrows_category R, Scheme.ofArrows_mem_smallEtaleTopology_iff,
      Set.eq_univ_iff_forall] at h
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (h x)
    exact ⟨_, j.obj.hom, j.property, hj⟩
  · intro h
    rw [← Sieve.ofArrows_category R, Scheme.ofArrows_mem_smallEtaleTopology_iff,
      Set.eq_univ_iff_forall]
    intro x
    obtain ⟨V, g, hg, hx⟩ := h x
    exact Set.mem_iUnion.mpr ⟨⟨Over.mk g, hg⟩, hx⟩

variable {S T : Scheme.{u}} (i : S ⟶ T) [IsClosedImmersion i]

private theorem change_fst {V U : T.Etale} (g : V ⟶ U) :
    ((etaleBaseChange i).map g).left ≫ pullback.fst U.hom i =
      pullback.fst V.hom i ≫ g.left := by
  simp only [etaleBaseChange, MorphismProperty.Over.pullback_map_left, pullback.lift_fst]

private theorem change_snd {V U : T.Etale} (g : V ⟶ U) :
    ((etaleBaseChange i).map g).left ≫ pullback.snd U.hom i = pullback.snd V.hom i := by
  simp only [etaleBaseChange, MorphismProperty.Over.pullback_map_left, pullback.lift_snd]

private theorem localLift_off_support {F G : Sheaf S.smallEtaleTopology A.{u}}
    (α : F ⟶ G) (U : T.Etale) (s : G.obj.obj (op ((etaleBaseChange i).obj U)))
    (x : U.left) (hx : x ∉ Set.range (pullback.fst U.hom i)) :
    ∃ (V : T.Etale) (g : V ⟶ U), x ∈ Set.range g.left ∧
      ∃ b : F.obj.obj (op ((etaleBaseChange i).obj V)),
        α.hom.app _ b = G.obj.map ((etaleBaseChange i).map g).op s := by
  let p := pullback.fst U.hom i
  let O : U.left.Opens := ⟨(Set.range p)ᶜ, p.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let V := openObject U O
  let g := openArrow U O
  have hEmpty : IsEmpty ((etaleBaseChange i).obj V).left := by
    refine ⟨fun y ↦ ?_⟩
    have h := congrArg (fun f : ((etaleBaseChange i).obj V).left ⟶ U.left ↦ f y)
      (change_fst i g)
    have hy : g.left (pullback.fst V.hom i y) ∉ Set.range p :=
      (pullback.fst V.hom i y : O).property
    exact hy ⟨((etaleBaseChange i).map g).left y, h⟩
  letI : IsEmpty ((etaleBaseChange i).obj V).left := hEmpty
  letI := subsingleton_sections_of_empty G ((etaleBaseChange i).obj V)
  exact ⟨V, g, ⟨⟨x, hx⟩, rfl⟩, 0, Subsingleton.elim _ _⟩

set_option maxHeartbeats 1500000 in
private theorem localLift_on_support (r : T ⟶ S) (hir : i ≫ r = 𝟙 S)
    {F G : Sheaf S.smallEtaleTopology A.{u}} (α : F ⟶ G) [Sheaf.IsLocallySurjective α]
    (U : T.Etale) (s : G.obj.obj (op ((etaleBaseChange i).obj U)))
    (x : U.left) (x' : ((etaleBaseChange i).obj U).left) (hx : pullback.fst U.hom i x' = x) :
    ∃ (V : T.Etale) (g : V ⟶ U), x ∈ Set.range g.left ∧
      ∃ b : F.obj.obj (op ((etaleBaseChange i).obj V)),
        α.hom.app _ b = G.obj.map ((etaleBaseChange i).map g).op s := by
  have hCover := Presheaf.imageSieve_mem S.smallEtaleTopology α.hom
    (U := op ((etaleBaseChange i).obj U)) s
  obtain ⟨W, k, hk, y, hy⟩ :=
    (cover_iff_points (Presheaf.imageSieve α.hom s)).mp hCover x'
  obtain ⟨b, hb⟩ := hk
  obtain ⟨V, v, hv, t, ht, htv⟩ := exists_refinement U.hom i r k.left hir
  letI : Etale v := hv
  let V' : T.Etale := Scheme.Etale.mk (v ≫ U.hom)
  let g : V' ⟶ U := MorphismProperty.Over.homMk v rfl
  let e : W ≅ (etaleBaseChange i).obj V' := MorphismProperty.Over.isoMk ht.isoPullback (by
    change ht.isoPullback.hom ≫ pullback.snd (v ≫ U.hom) i = W.hom
    exact ht.isoPullback_hom_snd.trans (MorphismProperty.Over.w k))
  have hNat : e.hom ≫ (etaleBaseChange i).map g = k := by
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext
    · change (ht.isoPullback.hom ≫ ((etaleBaseChange i).map g).left) ≫ pullback.fst U.hom i =
        k.left ≫ pullback.fst U.hom i
      rw [Category.assoc, change_fst]
      change ht.isoPullback.hom ≫ pullback.fst (v ≫ U.hom) i ≫ v = _
      rw [ht.isoPullback_hom_fst_assoc]
      exact htv
    · change (ht.isoPullback.hom ≫ ((etaleBaseChange i).map g).left) ≫ pullback.snd U.hom i =
        k.left ≫ pullback.snd U.hom i
      rw [Category.assoc, change_snd]
      change ht.isoPullback.hom ≫ pullback.snd (v ≫ U.hom) i = _
      rw [ht.isoPullback_hom_snd]
  have hInv : e.inv ≫ k = (etaleBaseChange i).map g := by
    rw [← hNat, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  refine ⟨V', g, ⟨t y, ?_⟩, F.obj.map e.inv.op b, ?_⟩
  · have h := congrArg (fun f : W.left ⟶ U.left ↦ f y) htv
    change v (t y) = pullback.fst U.hom i (k.left y) at h
    change v (t y) = x
    rw [h, hy, hx]
  · rw [NatTrans.naturality_apply, hb, ← ConcreteCategory.comp_apply, ← G.obj.map_comp,
      ← op_comp, hInv]

/-- The actual direct image preserves local surjectivity along a split closed immersion. -/
theorem map_locallySurjective (r : T ⟶ S) (hir : i ≫ r = 𝟙 S)
    {F G : Sheaf S.smallEtaleTopology A.{u}} (α : F ⟶ G) [Sheaf.IsLocallySurjective α] :
    Sheaf.IsLocallySurjective ((directImage i A.{u}).map α) where
  imageSieve_mem {U} s := by
    apply (cover_iff_points _).2
    intro x
    by_cases hx : x ∈ Set.range (pullback.fst U.hom i)
    · obtain ⟨x', hx'⟩ := hx
      obtain ⟨V, g, hg, b, hb⟩ := localLift_on_support i r hir α U s x x' hx'
      exact ⟨V, g, ⟨b, hb⟩, hg⟩
    · obtain ⟨V, g, hg, b, hb⟩ := localLift_off_support i α U s x hx
      exact ⟨V, g, ⟨b, hb⟩, hg⟩

/-- In particular, this native direct image takes epimorphisms to epimorphisms. -/
theorem map_epi (r : T ⟶ S) (hir : i ≫ r = 𝟙 S)
    {F G : Sheaf S.smallEtaleTopology A.{u}} (α : F ⟶ G) [Epi α] :
    Epi ((directImage i A.{u}).map α) := by
  letI : Sheaf.IsLocallySurjective α := of_epi α
  letI : Sheaf.IsLocallySurjective ((directImage i A.{u}).map α) :=
    map_locallySurjective i r hir α
  infer_instance

end
end ManuscriptAudit.SplitClosedEtaleDirectImage

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.SplitClosedEtaleDirectImage.map_locallySurjective,
      ``ManuscriptAudit.SplitClosedEtaleDirectImage.map_epi] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
