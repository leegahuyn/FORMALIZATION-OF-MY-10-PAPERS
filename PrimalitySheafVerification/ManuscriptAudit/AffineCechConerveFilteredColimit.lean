import Lean.Util.CollectAxioms
import Mathlib.AlgebraicTopology.CechNerve
import Mathlib.CategoryTheory.Limits.Comma
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Adjunction.Limits

/-! The chosen affine algebra Čech conerve commutes with actual
colimits of arrows degree by degree. -/

namespace ManuscriptAudit.AffineCechConerveFilteredColimit

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {J C : Type*} [Category* J] [Category* C] [HasFiniteColimits C]
  [HasColimitsOfShape J C]

/-- A cocone of arrows is colimiting if both original sides are
colimiting, with the actual specified limit arrow. -/
def isColimit_of_sides {F : J ⥤ Arrow C} (c : Cocone F)
    (hL : IsColimit ((Arrow.leftFunc : Arrow C ⥤ C).mapCocone c))
    (hR : IsColimit ((Arrow.rightFunc : Arrow C ⥤ C).mapCocone c)) : IsColimit c where
  desc s := Arrow.homMk
    (hL.desc ((Arrow.leftFunc : Arrow C ⥤ C).mapCocone s))
    (hR.desc ((Arrow.rightFunc : Arrow C ⥤ C).mapCocone s)) (by
      apply hL.hom_ext
      intro i
      have hl : (c.ι.app i).left ≫ hL.desc ((Arrow.leftFunc : Arrow C ⥤ C).mapCocone s) =
          (s.ι.app i).left := hL.fac _ i
      have hr : (c.ι.app i).right ≫ hR.desc ((Arrow.rightFunc : Arrow C ⥤ C).mapCocone s) =
          (s.ι.app i).right := hR.fac _ i
      change (c.ι.app i).left ≫ _ = (c.ι.app i).left ≫ c.pt.hom ≫ _
      rw [← Category.assoc, hl]
      have hw : (c.ι.app i).left ≫ c.pt.hom =
          (F.obj i).hom ≫ (c.ι.app i).right := (c.ι.app i).w
      rw [← Category.assoc, hw, Category.assoc, hr]
      exact (s.ι.app i).w)
  fac s j := by
    apply Arrow.hom_ext
    · exact hL.fac ((Arrow.leftFunc : Arrow C ⥤ C).mapCocone s) j
    · exact hR.fac ((Arrow.rightFunc : Arrow C ⥤ C).mapCocone s) j
  uniq s m hm := by
    apply Arrow.hom_ext
    · exact hL.uniq ((Arrow.leftFunc : Arrow C ⥤ C).mapCocone s) m.left
        (fun j ↦ congrArg (fun q ↦ q.left) (hm j))
    · exact hR.uniq ((Arrow.rightFunc : Arrow C ⥤ C).mapCocone s) m.right
        (fun j ↦ congrArg (fun q ↦ q.right) (hm j))

/-- Evaluation of the actual algebra conerve at one degree. -/
abbrev degree (n : ℕ) : Arrow C ⥤ C :=
  CosimplicialObject.cechConerve ⋙ (evaluation SimplexCategory C).obj ⦋n⦌

set_option maxHeartbeats 4200000 in
/-- The actual affine self-intersection ring diagrams retain the
same colimit arrow in every degree. -/
def isColimit_degree {F : J ⥤ Arrow C} {c : Cocone F} (hc : IsColimit c) (n : ℕ) :
    IsColimit ((degree n).mapCocone c) := by
  let E : Arrow C ⥤ CosimplicialObject.Augmented C := CosimplicialObject.augmentedCechConerve
  let D : CosimplicialObject.Augmented C ⥤ CosimplicialObject C := CosimplicialObject.Augmented.drop
  letI : E.IsLeftAdjoint := (CosimplicialObject.cechConerveAdjunction (C := C)).isLeftAdjoint
  letI : HasColimitsOfShape J (CosimplicialObject C) :=
    inferInstanceAs (HasColimitsOfShape J (SimplexCategory ⥤ C))
  letI : PreservesColimitsOfShape J (CosimplicialObject.const C) :=
    inferInstanceAs (PreservesColimitsOfShape J (Functor.const SimplexCategory : C ⥤ SimplexCategory ⥤ C))
  letI : PreservesColimitsOfShape J D :=
    inferInstanceAs (PreservesColimitsOfShape J (Comma.snd (CosimplicialObject.const C)
      (𝟭 (CosimplicialObject C))))
  let V : CosimplicialObject C ⥤ C := (evaluation SimplexCategory C).obj ⦋n⦌
  letI : PreservesColimitsOfShape J V :=
    inferInstanceAs (PreservesColimitsOfShape J ((evaluation SimplexCategory C).obj ⦋n⦌))
  change IsColimit (V.mapCocone (D.mapCocone (E.mapCocone c)))
  exact isColimitOfPreserves V (isColimitOfPreserves D (isColimitOfPreserves E hc))

end
end ManuscriptAudit.AffineCechConerveFilteredColimit

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineCechConerveFilteredColimit.isColimit_of_sides,
      ``ManuscriptAudit.AffineCechConerveFilteredColimit.isColimit_degree] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
