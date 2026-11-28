import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineCechRelativeArrowColimit
import PrimalitySheafVerification.ManuscriptAudit.AffineStageFixedCoproductLimits

/-! Base changes of a fixed affine cover give a genuine arrow
colimit along the actual tower of refining base rings. -/

namespace ManuscriptAudit.AffineCechModelArrowColimit

open CategoryTheory CategoryTheory.Limits
open AffineCechRelativeArrowColimit (isColimit_forgetBase)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A B : CommRingCat.{u}} (k : A ⟶ B) (E : Under B)

abbrev left (U : Under B) : U ⟶ U ⨿ E := coprod.inl

/-- The actual affine cover of an intermediate base is its coproduct
under the base of the fixed model. -/
def arrows : Under B ⥤ Arrow (Under A) where
  obj U := Arrow.mk ((Under.map k).map (left E U))
  map {U V} f := Arrow.homMk ((Under.map k).map f)
    ((Under.map k).map (coprod.map f (𝟙 E))) (by
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg (Under.map k).map (coprod.inl_map f (𝟙 E)).symm)
  map_id U := by
    apply Arrow.hom_ext <;> simp
  map_comp f g := by
    apply Arrow.hom_ext
    · exact (Under.map k).map_comp f g
    · change (Under.map k).map (coprod.map (f ≫ g) (𝟙 E)) =
        (Under.map k).map (coprod.map f (𝟙 E)) ≫ (Under.map k).map (coprod.map g (𝟙 E))
      rw [← Functor.map_comp]
      congr 1
      apply coprod.hom_ext <;> simp

variable {J : Type*} [Category* J] [IsFiltered J] [HasColimitsOfShape J (Under A)]
  {D : J ⥤ Under B} {c : Cocone D}

set_option maxHeartbeats 4300000 in
/-- Both sides of the modeled affine cover have the actual colimit. -/
def isColimit_arrows (hc : IsColimit c) :
    IsColimit ((arrows k E).mapCocone c) := by
  apply AffineCechConerveFilteredColimit.isColimit_of_sides
  · exact isColimit_forgetBase k hc
  · exact isColimit_forgetBase k (AffineStageFixedCoproductLimits.isColimit hc E)

end
end ManuscriptAudit.AffineCechModelArrowColimit

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineCechModelArrowColimit.isColimit_arrows
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
