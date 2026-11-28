import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.Filtered.Basic
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleStageCoequalizer

/-! The objects are actual affine étale stages of a chart, and the
arrows are actual algebra homomorphisms commuting with the chart. -/

namespace ManuscriptAudit.AffineEtaleStageCategory

open CategoryTheory CategoryTheory.Limits
open Algebra.TensorProduct
open scoped TensorProduct

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- An actual affine stage over the base, with a map to the chart ring. -/
structure Stage where
  carrier : Type u
  [ring : CommRing carrier]
  [algebra : Algebra A carrier]
  [isEtale : Algebra.Etale A carrier]
  toChart : carrier →ₐ[A] B

attribute [instance] Stage.ring Stage.algebra Stage.isEtale

/-- The actual algebra map specifies its stage object. -/
def Stage.of {C : Type u} [CommRing C] [Algebra A C] [Algebra.Etale A C] (g : C →ₐ[A] B) :
    Stage A B where
  carrier := C
  ring := inferInstance
  algebra := inferInstance
  isEtale := inferInstance
  toChart := g

instance : Category.{u} (Stage A B) where
  Hom X Y := {g : X.carrier →ₐ[A] Y.carrier // Y.toChart.comp g = X.toChart}
  id X := ⟨AlgHom.id A X.carrier, by ext x; rfl⟩
  comp f g := ⟨g.val.comp f.val, by rw [← AlgHom.comp_assoc, g.property, f.property]⟩
  id_comp f := Subtype.ext (by ext x; rfl)
  comp_id f := Subtype.ext (by ext x; rfl)
  assoc f g h := Subtype.ext (by ext x; rfl)

variable {A B}

abbrev hom {X Y : Stage A B} (f : X ⟶ Y) : X.carrier →ₐ[A] Y.carrier := f.val

theorem hom_toChart {X Y : Stage A B} (f : X ⟶ Y) (x : X.carrier) :
    Y.toChart (hom f x) = X.toChart x := DFunLike.congr_fun f.property x

/-- The ordinary ring diagram remembers the genuine stage maps. -/
def ringDiagram : Stage A B ⥤ CommRingCat.{u} where
  obj X := CommRingCat.of X.carrier
  map f := CommRingCat.ofHom (hom f).toRingHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Each stage maps into the actual chart, giving its canonical ring cocone. -/
def chartCocone : Cocone (ringDiagram (A := A) (B := B)) where
  pt := CommRingCat.of B
  ι :=
    { app := fun X ↦ CommRingCat.ofHom X.toChart.toRingHom
      naturality := by
        intro X Y f
        rw [Category.comp_id]
        exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom f.property) }

instance filtered : IsFiltered (Stage A B) where
  nonempty := ⟨Stage.of A B (Algebra.ofId A B)⟩
  cocone_objs X Y := by
    obtain ⟨ht, v, hX, hY⟩ := AffineEtaleStageCoequalizer.tensor_stage X.toChart Y.toChart
    letI : Algebra.Etale A (X.carrier ⊗[A] Y.carrier) := ht
    exact ⟨Stage.of A B v, ⟨includeLeft, hX⟩, ⟨includeRight, hY⟩, trivial⟩
  cocone_maps := by
    intro X Y f g
    obtain ⟨Q, hR, hA, hE, q, h, hEq, hQ⟩ := AffineEtaleStageCoequalizer.exists_coequalizer
      (hom f) (hom g) Y.toChart (f.property.trans g.property.symm)
    letI : CommRing Q := hR
    letI : Algebra A Q := hA
    letI : Algebra.Etale A Q := hE
    exact ⟨Stage.of A B h, ⟨q, hQ⟩, Subtype.ext hEq⟩

end
end ManuscriptAudit.AffineEtaleStageCategory

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleStageCategory.chartCocone,
      ``ManuscriptAudit.AffineEtaleStageCategory.filtered] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
