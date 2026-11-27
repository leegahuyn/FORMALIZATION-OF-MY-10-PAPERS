import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CyclicOrderQuotient
import PrimalitySheafVerification.ManuscriptAudit.EtaleObjectRestriction
import PrimalitySheafVerification.ManuscriptAudit.KummerRelativeUnitSections
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleCohomologyPresheaf
import PrimalitySheafVerification.ManuscriptAudit.SheafPresheafHOneBoundaryAdditive
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleUnitCohomology

/-! The Kummer boundary gives a natural unit presentation of degree one on affine PID charts. -/

namespace ManuscriptAudit.KummerChartBoundaryPresentation

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian Opposite
open KummerRelativeFull KummerRelativeUnitSections KummerUnitsSheaf
open OpenEtaleExtension SheafPresheafHOneBoundary

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

private abbrev C := AddCommGrpCat.{0}

variable {K R : Type} [Field K] [CommRing R]
variable {X : Scheme.{0}} (k : X ⟶ Spec (CommRingCat.of K))
variable (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
variable (d : ℕ) [NeZero (d : K)] (hd : 0 < d)

private abbrev Y := Scheme.Etale.mk j
private abbrev J := X.smallEtaleTopology
private abbrev S := sequence X d

/-- The actual additive Kummer boundary from coordinate units on an affine open. -/
def boundary : Additive Rˣ →+ (S (X := X) d).X₁.H' 1 (Y j) :=
  (boundaryAddHom (J (X := X)) (S (X := X) d) (sequence_shortExact k d hd) (Y j)).comp
    (coordinateUnitsIso d j).addCommGroupIsoToAddEquiv.symm.toAddMonoidHom

/-- On a PID chart the actual boundary is onto. -/
theorem boundary_surjective [IsDomain R] [IsPrincipalIdealRing R] :
    Function.Surjective (boundary k j d hd) := by
  let F := (S (X := X) d).X₂
  let e := (restriction j C).mapIso (unitsIso (X := X) d).symm ≪≫
    EtaleObjectRestriction.restrictionUnitsIso j
  let h := openCohomologyPresheafEquiv j F 1
  let g := ((Sheaf.functorH (Spec (CommRingCat.of R)).smallEtaleTopology 1).mapIso e)
    .addCommGroupIsoToAddEquiv
  let hR := KummerUnitsSheaf.unitHOne_subsingleton_of_pid R
  have hMiddle : Subsingleton (F.H' 1 (Y j)) :=
    ⟨fun x y ↦ h.injective (g.injective (hR.elim _ _))⟩
  exact (boundaryAddHom_surjective (J (X := X)) _ _ _ hMiddle).comp
    (coordinateUnitsIso d j).addCommGroupIsoToAddEquiv.symm.surjective

/-- The kernel is exactly the subgroup of coordinate dth powers. -/
theorem boundary_ker :
    (boundary k j d hd).ker = (CyclicOrderQuotient.nsmulMap (B := Additive Rˣ) d).range := by
  let e := coordinateUnitsIso d j
  let hS := sequence_shortExact k d hd
  ext z
  change boundaryOfSection (J (X := X)) (S (X := X) d) hS (Y j) (e.inv z) = 0 ↔
    ∃ w : Additive Rˣ, d • w = z
  rw [boundaryOfSection_eq_zero_iff]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨e.hom w, ?_⟩
    have h := congrArg e.hom ((coordinateUnitsIso_power (d := d) w).symm.trans hw)
    rwa [map_nsmul, Iso.inv_hom_id_apply] at h
  · rintro ⟨w, hw⟩
    refine ⟨e.inv w, ?_⟩
    apply e.addCommGroupIsoToAddEquiv.injective
    change e.hom ((S (X := X) d).g.hom.app (op (Y j)) (e.inv w)) = e.hom (e.inv z)
    rwa [coordinateUnitsIso_power, map_nsmul, Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]

variable {T : Type} [CommRing T] (r : CommRingCat.of R ⟶ CommRingCat.of T)
variable [IsOpenImmersion (Spec.map r)]

/-- Čech restriction on the genuine Kummer cohomology presheaf is compatible with the unit map. -/
theorem boundary_natural :
    (boundary k (Spec.map r ≫ j) d hd).comp (ringUnits.map r).hom =
      (((S (X := X) d).X₁.cohomologyPresheaf 1).map (chartArrow r j).op).hom.comp
        (boundary k j d hd) := by
  apply AddMonoidHom.ext
  intro u
  let U := Y j
  let V := Y (Spec.map r ≫ j)
  let e := coordinateUnitsIso d j
  let e' := coordinateUnitsIso d (Spec.map r ≫ j)
  let hS := sequence_shortExact k d hd
  let a := chartArrow r j
  change boundaryOfSection (J (X := X)) (S (X := X) d) hS V (e'.inv ((ringUnits.map r) u)) =
    ((S (X := X) d).X₁.cohomologyPresheaf 1).map a.op
      (boundaryOfSection (J (X := X)) (S (X := X) d) hS U (e.inv u))
  rw [boundaryOfSection_restrict]
  congr 1
  apply e'.addCommGroupIsoToAddEquiv.injective
  change e'.hom (e'.inv ((ringUnits.map r) u)) =
    e'.hom ((S (X := X) d).X₃.obj.map a.op (e.inv u))
  have h := ConcreteCategory.congr_hom (coordinateUnitsIso_restrict d r j) (e.inv u)
  change e'.hom ((S (X := X) d).X₃.obj.map a.op (e.inv u)) = (ringUnits.map r) (e.hom (e.inv u)) at h
  rw [Iso.inv_hom_id_apply] at h ⊢
  exact h.symm

end
end ManuscriptAudit.KummerChartBoundaryPresentation

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.KummerChartBoundaryPresentation.boundary_surjective,
      ``ManuscriptAudit.KummerChartBoundaryPresentation.boundary_ker,
      ``ManuscriptAudit.KummerChartBoundaryPresentation.boundary_natural] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
