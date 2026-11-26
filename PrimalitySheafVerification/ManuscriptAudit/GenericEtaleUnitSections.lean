import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Comma.Over.Pullback
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleBaseChange
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleUnitSheaf

/-!
# Sections of the small étale direct image of units at a generic point

There is a canonical map from units to the direct image of units under
any scheme morphism. For the fraction-field point of an affine scheme,
the value of that direct image on an affine étale chart is the unit group
of its actual tensor-product generic fiber.
-/

namespace ManuscriptAudit.GenericEtaleUnitSections

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open KummerUnitsSheaf SmallEtaleBaseChange
open scoped TensorProduct

noncomputable section

private def underlying (X : Scheme.{0}) : X.Etale ⥤ Scheme.{0} :=
  Scheme.Etale.forget X ⋙ Over.forget X

private def projection {X Y : Scheme.{0}} (f : X ⟶ Y) :
    etaleBaseChange f ⋙ underlying X ⟶ underlying Y where
  app U := pullback.fst U.hom f
  naturality := by
    intro U V h
    change ((Over.pullback f).map ((Scheme.Etale.forget Y).map h)).left ≫
        pullback.fst V.hom f = pullback.fst U.hom f ≫ h.left
    have hw : (pullback.fst U.hom f ≫ h.left) ≫ V.hom =
        pullback.snd U.hom f ≫ f := by
      rw [Category.assoc, h.w, pullback.condition]
    exact pullback.lift_fst _ _ hw

/-- The actual pullback of regular units gives a map into the direct image on
the small étale site. -/
def pullbackToDirectImage {X Y : Scheme.{0}} (f : X ⟶ Y) :
    fullCoordinateUnitSheaf Y ⟶ (directImage f AddCommGrpCat.{0}).obj (fullCoordinateUnitSheaf X) :=
  ⟨Functor.whiskerRight (projection f).op (Scheme.Γ ⋙ ringUnits)⟩

private abbrev algebraSpecMap (A B : Type) [CommRing A] [CommRing B] [Algebra A B] :
    Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A B))

/-- The actual affine scheme of an étale algebra regarded as a small étale object. -/
def algebraEtaleObject (A B : Type) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.Etale A B] : (Spec (CommRingCat.of A)).Etale := by
  letI : Etale (algebraSpecMap A B) := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr inferInstance)
  exact Scheme.Etale.mk (algebraSpecMap A B)

/-- The actual direct image along the spectrum of the fraction-field map. -/
def genericUnitImage (A F : Type) [CommRing A] [IsDomain A] [Field F]
    [Algebra A F] [IsFractionRing A F] :
    Sheaf (Spec (CommRingCat.of A)).smallEtaleTopology AddCommGrpCat.{0} :=
  (directImage (algebraSpecMap A F) AddCommGrpCat.{0}).obj
    (fullCoordinateUnitSheaf (Spec (CommRingCat.of F)))

/-- The generic-point direct image, evaluated on an actual affine étale
chart, is canonically the units of its tensor-product generic fiber. -/
def genericUnitSectionsIso (A B F : Type) [CommRing A] [IsDomain A] [CommRing B] [Field F]
    [Algebra A B] [Algebra A F] [IsFractionRing A F] [Algebra.Etale A B] :
    (genericUnitImage A F).obj.obj (op (algebraEtaleObject A B)) ≅
      AddCommGrpCat.of (Additive (F ⊗[A] B)ˣ) := by
  let W := (etaleBaseChange (algebraSpecMap A F)).obj (algebraEtaleObject A B)
  let e : W.left ≅ Spec (CommRingCat.of (F ⊗[A] B)) := by
    change pullback (algebraSpecMap A B) (algebraSpecMap A F) ≅ _
    exact pullbackSymmetry (algebraSpecMap A B) (algebraSpecMap A F) ≪≫ pullbackSpecIso A F B
  change ringUnits.obj (Scheme.Γ.obj (op W.left)) ≅ _
  exact ringUnits.mapIso ((Scheme.Γ.mapIso e.symm.op) ≪≫ Scheme.ΓSpecIso _)

end

end ManuscriptAudit.GenericEtaleUnitSections

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.GenericEtaleUnitSections.pullbackToDirectImage,
      ``ManuscriptAudit.GenericEtaleUnitSections.genericUnitSectionsIso] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
