import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import PrimalitySheafVerification.ManuscriptAudit.AffineCechConerveFilteredColimit
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleStageAlgebraColimit

/-! The arrows of a filtered relative affine diagram converge to the
actual original chart arrow, with the base ring held fixed. -/

namespace ManuscriptAudit.AffineCechRelativeArrowColimit

open CategoryTheory CategoryTheory.Limits

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A B : CommRingCat.{u}} (k : A ⟶ B)

abbrev base := Under.mk k
abbrev forgetBase := Under.map k

/-- A relative algebra remembers its actual map from the specified base. -/
abbrev coverArrow (R : Under B) : base k ⟶ (forgetBase k).obj R :=
  Under.homMk R.hom rfl

/-- Display each object as the actual arrow of affine algebras. -/
def arrows : Under B ⥤ Arrow (Under A) where
  obj R := Arrow.mk (coverArrow k R)
  map f := Arrow.homMk (𝟙 _) ((forgetBase k).map f) (by
    rw [Category.id_comp]
    apply (Under.forget A).map_injective
    exact (Under.w f).symm)
  map_id _ := by
    apply Arrow.hom_ext
    · rfl
    · exact (forgetBase k).map_id _
  map_comp f g := by
    apply Arrow.hom_ext
    · simp
    · exact (forgetBase k).map_comp f g

variable {J : Type*} [Category* J] [IsFiltered J]
  {D : J ⥤ Under B} {c : Cocone D}

/-- Forgetting the relative base while retaining the original A-structure
preserves the actual filtered ring colimit. -/
def isColimit_forgetBase (hc : IsColimit c) :
    IsColimit ((forgetBase k).mapCocone c) := by
  letI : Nonempty J := IsFiltered.nonempty
  letI : IsConnected J := IsFiltered.isConnected J
  apply AffineEtaleStageAlgebraColimit.liftIsColimit
  exact isColimitOfPreserves (Under.forget B) hc

set_option maxHeartbeats 4000000 in
/-- The actual arrow cocone is a colimit in the arrow category. -/
def isColimit_arrows [HasColimitsOfShape J (Under A)] (hc : IsColimit c) :
    IsColimit ((arrows k).mapCocone c) := by
  letI : IsConnected J := IsFiltered.isConnected J
  exact AffineCechConerveFilteredColimit.isColimit_of_sides _
    (isColimitConstCocone J (base k)) (isColimit_forgetBase k hc)

end
end ManuscriptAudit.AffineCechRelativeArrowColimit

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineCechRelativeArrowColimit.isColimit_arrows
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
