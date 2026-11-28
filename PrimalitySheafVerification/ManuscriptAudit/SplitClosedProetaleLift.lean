import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.SplitClosedProetaleRefinement
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAffineSingletonLift
import PrimalitySheafVerification.ManuscriptAudit.ProetaleBaseChange

/-! A single affine refinement lifts a section over the complete closed fiber. -/

namespace ManuscriptAudit.SplitClosedProetaleLift

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleBaseChange

noncomputable section
universe u v

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev C (X : Scheme.{u}) := Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{v}

variable {S T : Scheme.{u}} [IsAffine S]
variable (i : S ⟶ T) [IsClosedImmersion i]
variable (r : T ⟶ S) (hir : i ≫ r = 𝟙 S)

private theorem change_fst {V U : T.ProEt} (g : V ⟶ U) :
    ((baseChange i).map g).left ≫ pullback.fst U.hom i =
      pullback.fst V.hom i ≫ g.left := by
  simp only [baseChange, MorphismProperty.Over.pullback_map_left, pullback.lift_fst]

private theorem change_snd {V U : T.ProEt} (g : V ⟶ U) :
    ((baseChange i).map g).left ≫ pullback.snd U.hom i = pullback.snd V.hom i := by
  simp only [baseChange, MorphismProperty.Over.pullback_map_left, pullback.lift_snd]

/-- A single affine ambient refinement has lifts on the full part supported
over the closed subscheme and covers each point on that support. -/
theorem exists_on_support {F G : C.{u,v} S}
    (α : F ⟶ G) [Sheaf.IsLocallySurjective α] (U : T.ProEt) [IsAffine U.left]
    (s : G.obj.obj (op ((baseChange i).obj U))) :
    ∃ (V : T.ProEt) (g : V ⟶ U), IsAffine V.left ∧
      Set.range (pullback.fst U.hom i) ⊆ Set.range g.left ∧
      ∃ b : F.obj.obj (op ((baseChange i).obj V)),
        α.hom.app _ b = G.obj.map ((baseChange i).map g).op s := by
  letI : WeaklyEtale U.hom := U.prop
  letI : IsAffine ((baseChange i).obj U).left :=
    isAffine_of_isAffineHom (pullback.fst U.hom i)
  obtain ⟨W, k, hA, hW, hS, _, b, hb⟩ :=
    ProetaleAffineSingletonLift.exists_singleton_cover_lift α s
  letI : IsAffine W.left := hA
  letI : WeaklyEtale k.left := hW
  obtain ⟨V, hvA, v, hv, t, ht, htv⟩ :=
    SplitClosedProetaleRefinement.exists_refinement U.hom i r k.left hir
  letI : WeaklyEtale v := hv
  let V' : T.ProEt := Scheme.ProEt.mk (v ≫ U.hom)
  let g : V' ⟶ U := MorphismProperty.Over.homMk v rfl
  let e : W ≅ (baseChange i).obj V' := MorphismProperty.Over.isoMk ht.isoPullback (by
    change ht.isoPullback.hom ≫ pullback.snd (v ≫ U.hom) i = W.hom
    exact ht.isoPullback_hom_snd.trans (MorphismProperty.Over.w k))
  have hNat : e.hom ≫ (baseChange i).map g = k := by
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext
    · change (ht.isoPullback.hom ≫ ((baseChange i).map g).left) ≫ pullback.fst U.hom i =
        k.left ≫ pullback.fst U.hom i
      rw [Category.assoc, change_fst]
      change ht.isoPullback.hom ≫ pullback.fst (v ≫ U.hom) i ≫ v = _
      rw [ht.isoPullback_hom_fst_assoc]
      exact htv
    · change (ht.isoPullback.hom ≫ ((baseChange i).map g).left) ≫ pullback.snd U.hom i =
        k.left ≫ pullback.snd U.hom i
      rw [Category.assoc, change_snd]
      change ht.isoPullback.hom ≫ pullback.snd (v ≫ U.hom) i = _
      rw [ht.isoPullback_hom_snd]
  have hInv : e.inv ≫ k = (baseChange i).map g := by
    rw [← hNat, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  refine ⟨V', g, hvA, ?_, F.obj.map e.inv.op b, ?_⟩
  · rintro x ⟨x', rfl⟩
    obtain ⟨y, hy⟩ := hS.surj x'
    refine ⟨t y, ?_⟩
    have h := congrArg (fun f : W.left ⟶ U.left ↦ f y) htv
    change v (t y) = pullback.fst U.hom i (k.left y) at h
    change v (t y) = pullback.fst U.hom i x'
    rw [h, hy]
  · rw [NatTrans.naturality_apply, hb, ← ConcreteCategory.comp_apply,
      ← G.obj.map_comp, ← op_comp, hInv]

end
end ManuscriptAudit.SplitClosedProetaleLift

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.SplitClosedProetaleLift.exists_on_support
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{name} depends on unexpected axioms {ax}"
  logInfo m!"{name} uses {ax}"
