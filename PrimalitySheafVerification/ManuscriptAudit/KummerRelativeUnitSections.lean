import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.KummerRelativeFull

/-! On affine objects of the actual small étale site, coordinate units are the
sections of the full Kummer unit terms. Their restrictions are native ring maps. -/

namespace ManuscriptAudit.KummerRelativeUnitSections

open AlgebraicGeometry CategoryTheory Opposite
open KummerRelativeFull KummerUnitsSheaf

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{0}} {R S : CommRingCat.{0}} (d : ℕ)

private abbrev C := AddCommGrpCat.{0}
private abbrev UnitTerm := (sequence X d).X₂

/-- A section on an affine étale object is a unit in its displayed coordinate ring. -/
def coordinateUnitsIso (j : Spec R ⟶ X) [Etale j] :
    (UnitTerm d (X := X)).obj.obj (op (Scheme.Etale.mk j)) ≅
      AddCommGrpCat.of (Additive Rˣ) := by
  let E := (sheafToPresheaf X.smallEtaleTopology C).mapIso (unitsIso (X := X) d).symm
  exact E.app (op (Scheme.Etale.mk j)) ≪≫ ringUnits.mapIso (Scheme.ΓSpecIso R)

variable (r : R ⟶ S) (j : Spec R ⟶ X) [Etale j] [Etale (Spec.map r)]
variable [Etale (Spec.map r ≫ j)]

/-- The arrow induced by a ring map between affine étale objects over the same base. -/
def chartArrow :
    Scheme.Etale.mk (Spec.map r ≫ j) ⟶ Scheme.Etale.mk j :=
  MorphismProperty.Over.homMk (Spec.map r) rfl

/-- Restricting sections and recording coordinate units commute with change of rings. -/
theorem coordinateUnitsIso_restrict :
    (UnitTerm d (X := X)).obj.map (chartArrow r j).op ≫
        (coordinateUnitsIso d (Spec.map r ≫ j)).hom =
      (coordinateUnitsIso d j).hom ≫ ringUnits.map r := by
  let a := (chartArrow r j).op
  let E := (sheafToPresheaf X.smallEtaleTopology C).mapIso (unitsIso (X := X) d).symm
  have h : (fullCoordinateUnits X).map a ≫ (ringUnits.mapIso (Scheme.ΓSpecIso S)).hom =
      (ringUnits.mapIso (Scheme.ΓSpecIso R)).hom ≫ ringUnits.map r := by
    change ringUnits.map (Spec.map r).appTop ≫ ringUnits.map (Scheme.ΓSpecIso S).hom =
      ringUnits.map (Scheme.ΓSpecIso R).hom ≫ ringUnits.map r
    rw [← Functor.map_comp, ← Functor.map_comp, Scheme.ΓSpecIso_naturality]
  change (UnitTerm d (X := X)).obj.map a ≫
      E.hom.app _ ≫ (ringUnits.mapIso (Scheme.ΓSpecIso S)).hom =
    (E.hom.app _ ≫ (ringUnits.mapIso (Scheme.ΓSpecIso R)).hom) ≫ ringUnits.map r
  rw [← Category.assoc, E.hom.naturality a, Category.assoc, h, Category.assoc]

variable {d} in
/-- Passing to coordinate units turns a pointwise Kummer lift into an actual root. -/
theorem coordinateUnitsIso_power {U : X.Etale}
    (x : (UnitTerm d (X := X)).obj.obj (op U)) :
    (sequence X d).g.hom.app (op U) x = d • x := by
  let P := sheafToPresheaf X.smallEtaleTopology C ⋙ (evaluation X.Etaleᵒᵖ C).obj (op U)
  have h := congrArg P.map (power_nsmul (X := X) d)
  change ((sequence X d).g.hom.app (op U)) = P.map (d • 𝟙 (UnitTerm d (X := X))) at h
  rw [Functor.map_nsmul, P.map_id] at h
  simpa using congrArg (fun f : P.obj (UnitTerm d (X := X)) ⟶ P.obj (UnitTerm d (X := X)) => f x) h

end
end ManuscriptAudit.KummerRelativeUnitSections

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.KummerRelativeUnitSections.coordinateUnitsIso_restrict,
      ``ManuscriptAudit.KummerRelativeUnitSections.coordinateUnitsIso_power] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
