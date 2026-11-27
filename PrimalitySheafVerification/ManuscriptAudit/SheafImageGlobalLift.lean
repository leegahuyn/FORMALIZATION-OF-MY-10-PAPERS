import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Abelian.Basic
import PrimalitySheafVerification.ManuscriptAudit.SheafSectionDifference

/-! Sections locally in a monomorphism's image glue to a unique global
preimage. In particular this applies to the categorical image of a map. -/

namespace ManuscriptAudit.SheafImageGlobalLift

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v w z

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{w}] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
variable {T : C} {I : Type z} (U : I → C) (a : ∀ i, U i ⟶ T)
variable (hCover : Sieve.ofArrows U a ∈ J T)
variable {F G : Sheaf J AddCommGrpCat.{w}}

private theorem restrict_restrict (P : Cᵒᵖ ⥤ AddCommGrpCat.{w}) {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : P.obj (op Z)) :
    P.map f.op (P.map g.op x) = P.map (f ≫ g).op x := by
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

include hCover in
/-- A section locally admitting preimages under a monomorphism admits a global preimage. -/
theorem exists_preimage_of_mono (m : F ⟶ G) [Mono m] (s : G.obj.obj (op T))
    (h : ∀ i, ∃ t : F.obj.obj (op (U i)), m.hom.app (op (U i)) t = G.obj.map (a i).op s) :
    ∃ t : F.obj.obj (op T), m.hom.app (op T) t = s := by
  choose t ht using h
  let A := AddCommGrpCat.{w}
  let P := F.obj ⋙ forget A
  let Q := G.obj ⋙ forget A
  have hFam : Presieve.Arrows.Compatible P a t := by
    intro i j V f g hfg
    change F.obj.map f.op (t i) = F.obj.map g.op (t j)
    apply SheafSectionDifference.section_injective m V
    rw [NatTrans.naturality_apply m.hom f.op, NatTrans.naturality_apply m.hom g.op, ht i, ht j,
      restrict_restrict, restrict_restrict, hfg]
  have hF : Presieve.IsSheaf J P :=
    (isSheaf_iff_isSheaf_of_type J _).mp ((sheafCompose J (forget A)).obj F).property
  have hG : Presieve.IsSheaf J Q :=
    (isSheaf_iff_isSheaf_of_type J _).mp ((sheafCompose J (forget A)).obj G).property
  let R := Presieve.ofArrows U a
  obtain ⟨b, hb, _⟩ := (Presieve.isSheafFor_arrows_iff (P := P) (π := a)).mp
    (hF.isSheafFor R hCover) t hFam
  refine ⟨b, (hG.isSheafFor R hCover).isSeparatedFor.ext ?_⟩
  rintro _ _ ⟨i⟩
  change G.obj.map (a i).op (m.hom.app (op T) b) = G.obj.map (a i).op s
  rw [← NatTrans.naturality_apply m.hom (a i).op b]
  exact (congrArg (m.hom.app (op (U i))) (hb i)).trans (ht i)

include hCover in
/-- A section admitting local lifts under the original map lies in its actual categorical image. -/
theorem exists_image_section (f : F ⟶ G) (s : G.obj.obj (op T))
    (h : ∀ i, ∃ t : F.obj.obj (op (U i)), f.hom.app (op (U i)) t = G.obj.map (a i).op s) :
    ∃ t : (Abelian.image f).obj.obj (op T), (Abelian.image.ι f).hom.app (op T) t = s := by
  apply exists_preimage_of_mono U a hCover (Abelian.image.ι f) s
  intro i
  obtain ⟨b, hb⟩ := h i
  refine ⟨(Abelian.factorThruImage f).hom.app (op (U i)) b, ?_⟩
  exact (ConcreteCategory.congr_hom
    (congrArg (fun g : F ⟶ G ↦ g.hom.app (op (U i))) (Abelian.image.fac f)) b).trans hb

end

end ManuscriptAudit.SheafImageGlobalLift

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.SheafImageGlobalLift.exists_image_section
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
