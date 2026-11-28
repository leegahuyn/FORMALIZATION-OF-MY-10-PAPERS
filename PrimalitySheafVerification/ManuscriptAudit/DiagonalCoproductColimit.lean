import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.IsLimit

/-! Diagonal binary coproducts of two diagrams commute with colimits,
by applying the given colimit property on the two canonical legs. -/

namespace ManuscriptAudit.DiagonalCoproductColimit

open CategoryTheory CategoryTheory.Limits

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {J C : Type*} [Category* J] [Category* C] [HasBinaryCoproducts C]
variable {F G : J ⥤ C}

/-- The two objects are taken at the same stage. -/
def diagram (F G : J ⥤ C) : J ⥤ C where
  obj j := F.obj j ⨿ G.obj j
  map f := coprod.map (F.map f) (G.map f)
  map_id j := by simp
  map_comp f g := by simp

/-- The stage-to-colimit maps are the actual coproduct of the two maps. -/
def cocone (cF : Cocone F) (cG : Cocone G) : Cocone (diagram F G) where
  pt := cF.pt ⨿ cG.pt
  ι :=
    { app := fun j ↦ coprod.map (cF.ι.app j) (cG.ι.app j)
      naturality := by
        intro i j f
        apply coprod.hom_ext
        · simp [diagram, cF.w f]
        · simp [diagram, cG.w f] }

private def leftCocone (s : Cocone (diagram F G)) : Cocone F where
  pt := s.pt
  ι :=
    { app := fun j ↦ coprod.inl ≫ s.ι.app j
      naturality := by
        intro i j f
        change F.map f ≫ (coprod.inl ≫ s.ι.app j) = (coprod.inl ≫ s.ι.app i) ≫ 𝟙 s.pt
        have h := congrArg (fun m ↦ coprod.inl ≫ m) (s.w f)
        have h' : F.map f ≫ (coprod.inl ≫ s.ι.app j) = coprod.inl ≫ s.ι.app i := by
          simpa only [diagram, Category.assoc, coprod.inl_map_assoc] using h
        exact h'.trans (Category.comp_id _).symm }

private def rightCocone (s : Cocone (diagram F G)) : Cocone G where
  pt := s.pt
  ι :=
    { app := fun j ↦ coprod.inr ≫ s.ι.app j
      naturality := by
        intro i j f
        change G.map f ≫ (coprod.inr ≫ s.ι.app j) = (coprod.inr ≫ s.ι.app i) ≫ 𝟙 s.pt
        have h := congrArg (fun m ↦ coprod.inr ≫ m) (s.w f)
        have h' : G.map f ≫ (coprod.inr ≫ s.ι.app j) = coprod.inr ≫ s.ι.app i := by
          simpa only [diagram, Category.assoc, coprod.inr_map_assoc] using h
        exact h'.trans (Category.comp_id _).symm }

set_option maxHeartbeats 2400000 in
/-- The coproduct of the two colimits is the colimit of the actual
stagewise coproducts. This applies in the category of rings under B
to the tensor-square terms of a Čech diagram. -/
def isColimit {cF : Cocone F} {cG : Cocone G} (hF : IsColimit cF) (hG : IsColimit cG) :
    IsColimit (cocone cF cG) where
  desc s := coprod.desc (hF.desc (leftCocone s)) (hG.desc (rightCocone s))
  fac s j := by
    apply coprod.hom_ext
    · simpa only [cocone, Category.assoc, coprod.inl_map_assoc, coprod.inl_desc, leftCocone]
        using hF.fac (leftCocone s) j
    · simpa only [cocone, Category.assoc, coprod.inr_map_assoc, coprod.inr_desc, rightCocone]
        using hG.fac (rightCocone s) j
  uniq s m hm := by
    change cF.pt ⨿ cG.pt ⟶ s.pt at m
    apply coprod.hom_ext
    · simp only [cocone, coprod.inl_desc]
      apply hF.hom_ext
      intro j
      rw [hF.fac]
      have h := congrArg (fun k ↦ coprod.inl ≫ k) (hm j)
      simpa only [cocone, Category.assoc, coprod.inl_map_assoc, leftCocone] using h
    · simp only [cocone, coprod.inr_desc]
      apply hG.hom_ext
      intro j
      rw [hG.fac]
      have h := congrArg (fun k ↦ coprod.inr ≫ k) (hm j)
      simpa only [cocone, Category.assoc, coprod.inr_map_assoc, rightCocone] using h

end
end ManuscriptAudit.DiagonalCoproductColimit

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.DiagonalCoproductColimit.isColimit
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
