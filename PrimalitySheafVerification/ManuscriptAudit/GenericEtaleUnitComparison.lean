import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.GenericEtaleUnitSections

/-!
# The affine chart of the generic-point unit map

The canonical map from the unit sheaf to its generic-point direct image
is the actual inclusion of units of the coordinate ring into the units
of the tensor-product generic fiber on every affine étale chart.
-/

namespace ManuscriptAudit.GenericEtaleUnitSections

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open KummerUnitsSheaf
open scoped TensorProduct

noncomputable section

set_option backward.isDefEq.respectTransparency false

private abbrev specAlgebraMap (A B : Type) [CommRing A] [CommRing B] [Algebra A B] :
    Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A B))

/-- The canonical unit map into the actual fraction-field direct image. -/
def genericPointUnitsHom (A F : Type) [CommRing A] [IsDomain A] [Field F]
    [Algebra A F] [IsFractionRing A F] :
    fullCoordinateUnitSheaf (Spec (CommRingCat.of A)) ⟶ genericUnitImage A F :=
  pullbackToDirectImage (specAlgebraMap A F)

/-- Evaluating the unit sheaf on an affine étale chart gives its coordinate units. -/
def affineUnitSectionsIso (A B : Type) [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.Etale A B] :
    (fullCoordinateUnitSheaf (Spec (CommRingCat.of A))).obj.obj (op (algebraEtaleObject A B)) ≅
      AddCommGrpCat.of (Additive Bˣ) :=
  ringUnits.mapIso (Scheme.ΓSpecIso (CommRingCat.of B))

/-- The actual generic-point map is induced by the tensor product's right inclusion. -/
theorem genericPointUnitsHom_onAffine (A B F : Type) [CommRing A] [IsDomain A] [CommRing B]
    [Field F] [Algebra A B] [Algebra A F] [IsFractionRing A F] [Algebra.Etale A B] :
    (genericPointUnitsHom A F).hom.app (op (algebraEtaleObject A B)) ≫
        (genericUnitSectionsIso A B F).hom =
      (affineUnitSectionsIso A B).hom ≫ ringUnits.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : B →ₐ[A] F ⊗[A] B).toRingHom) := by
  let j := specAlgebraMap A F
  let b := specAlgebraMap A B
  let T := CommRingCat.of (F ⊗[A] B)
  let i : CommRingCat.of B ⟶ T := CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : B →ₐ[A] F ⊗[A] B).toRingHom
  let e : pullback b j ≅ Spec T := pullbackSymmetry b j ≪≫ pullbackSpecIso A F B
  have he : e.hom ≫ Spec.map i = pullback.fst b j := by
    simp [e, i, b, j, specAlgebraMap, Category.assoc]
  have he' : e.inv ≫ pullback.fst b j = Spec.map i := by
    rw [← he, Iso.inv_hom_id_assoc]
  change ringUnits.map (pullback.fst b j).appTop ≫
      ringUnits.map (e.inv.appTop ≫ (Scheme.ΓSpecIso T).hom) =
    ringUnits.map (Scheme.ΓSpecIso (CommRingCat.of B)).hom ≫ ringUnits.map i
  rw [← ringUnits.map_comp, ← ringUnits.map_comp, ← Category.assoc,
    ← Scheme.Hom.comp_appTop, he', Scheme.ΓSpecIso_naturality]

end

end ManuscriptAudit.GenericEtaleUnitSections

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.GenericEtaleUnitSections.genericPointUnitsHom_onAffine
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
