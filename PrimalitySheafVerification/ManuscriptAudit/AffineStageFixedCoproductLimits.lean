import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Filtered.Basic
import PrimalitySheafVerification.ManuscriptAudit.DiagonalCoproductColimit

/-! Refining the base of a fixed cover and the fixed cover's self-intersection
gives two compatible colimit diagrams. -/

namespace ManuscriptAudit.AffineStageFixedCoproductLimits

open CategoryTheory CategoryTheory.Limits

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {J C : Type*} [Category* J] [Category* C] [HasBinaryCoproducts C]

private def constantCocone (E : C) : Cocone ((Functor.const J).obj E) where
  pt := E
  ι := { app := fun _ ↦ 𝟙 E }

private def constantIsColimit [IsFiltered J] (E : C) :
    IsColimit (constantCocone (J := J) E) where
  desc s := s.ι.app (Classical.choice IsFiltered.nonempty)
  fac s j := by
    let i : J := Classical.choice IsFiltered.nonempty
    change (𝟙 E) ≫ (s.ι.app i : E ⟶ s.pt) = s.ι.app j
    have hi := s.w (IsFiltered.leftToMax i j)
    have hj := s.w (IsFiltered.rightToMax i j)
    change 𝟙 E ≫ s.ι.app _ = s.ι.app i at hi
    change 𝟙 E ≫ s.ι.app _ = s.ι.app j at hj
    rw [Category.id_comp] at hi hj
    exact (Category.id_comp (s.ι.app i : E ⟶ s.pt)).trans (hi.symm.trans hj)
  uniq s m hm := by
    let i : J := Classical.choice IsFiltered.nonempty
    have h := hm i
    change 𝟙 E ≫ m = s.ι.app i at h
    simpa only [Category.id_comp] using h

/-- Attach the fixed cover ring on the right of each refining base ring. -/
abbrev diagram (F : J ⥤ C) (E : C) :=
  DiagonalCoproductColimit.diagram F ((Functor.const J).obj E)

/-- The limit cover ring is the coproduct with the fixed cover over the initial base. -/
abbrev cocone {F : J ⥤ C} (c : Cocone F) (E : C) : Cocone (diagram F E) :=
  DiagonalCoproductColimit.cocone c (constantCocone (J := J) E)

def isColimit [IsFiltered J] {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c) (E : C) :
    IsColimit (cocone c E) :=
  DiagonalCoproductColimit.isColimit hc (constantIsColimit E)

/-- A right-hand algebra map, including either overlap arrow, acts at all stages. -/
def map (F : J ⥤ C) {E H : C} (a : E ⟶ H) : diagram F E ⟶ diagram F H where
  app i := coprod.map (𝟙 (F.obj i)) a
  naturality {i j} ij := by
    change coprod.map (F.map ij) (𝟙 E) ≫ coprod.map (𝟙 (F.obj j)) a =
      coprod.map (𝟙 (F.obj i)) a ≫ coprod.map (F.map ij) (𝟙 H)
    apply coprod.hom_ext <;> simp

/-- A map into the fixed self-intersection commutes with every refinement. -/
theorem map_cocone {F : J ⥤ C} (c : Cocone F) {E H : C} (a : E ⟶ H) (i : J) :
    (cocone c E).ι.app i ≫ coprod.map (𝟙 c.pt) a =
      (map F a).app i ≫ (cocone c H).ι.app i := by
  change coprod.map (c.ι.app i) (𝟙 E) ≫ coprod.map (𝟙 c.pt) a =
    coprod.map (𝟙 (F.obj i)) a ≫ coprod.map (c.ι.app i) (𝟙 H)
  apply coprod.hom_ext <;> simp

end
end ManuscriptAudit.AffineStageFixedCoproductLimits

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineStageFixedCoproductLimits.isColimit,
      ``ManuscriptAudit.AffineStageFixedCoproductLimits.map_cocone] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
