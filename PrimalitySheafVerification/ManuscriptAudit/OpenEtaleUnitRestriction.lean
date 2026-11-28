import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleTerminalCohomology
import PrimalitySheafVerification.ManuscriptAudit.EtaleObjectRestriction

/-! Pullback on the actual unit cohomology along an open immersion
is the restriction at the corresponding native small étale object. -/

namespace ManuscriptAudit.OpenEtaleUnitRestriction

open AlgebraicGeometry CategoryTheory
open EtaleTwoOpenHOne EtaleTerminalCohomology OpenEtaleExtension KummerUnitsSheaf

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]

private abbrev C := AddCommGrpCat.{0}
private abbrev G (Y : Scheme.{0}) := fullCoordinateUnitSheaf Y
private abbrev T (Y : Scheme.{0}) := identityObject Y

/-- Restriction to an actual open leaves the unit sections on each
étale object as the same literal scheme units. -/
abbrev restrictUnitsIso : (restriction j C).obj (G X) ≅ G U :=
  EtaleObjectRestriction.restrictionUnitsIso j

/-- Actual open restriction evaluated from ambient cohomology at the open. -/
def cohomologyOnOpenEquiv (n : ℕ) :
    (G X).H' n (Scheme.Etale.mk j) ≃+ Sheaf.H (G U) n :=
  (openCohomologyPresheafEquiv j (G X) n).trans
    (((Sheaf.functorH U.smallEtaleTopology n).mapIso (restrictUnitsIso j)).addCommGroupIsoToAddEquiv)

/-- Pullback on true étale unit cohomology along the actual open immersion. -/
def unitCohomologyPullback (n : ℕ) : Sheaf.H (G X) n →+ Sheaf.H (G U) n :=
  (cohomologyOnOpenEquiv j n).toAddMonoidHom.comp
    ((((G X).cohomologyPresheaf n).map (openArrow j).op).hom.comp
      (terminalHEquiv X (G X) n).symm.toAddMonoidHom)

variable {j}

/-- An isomorphism of schemes yields the literal isomorphism of unit
cohomology by pullback on their small étale topologies. -/
def unitCohomologyIso (e : U ≅ X) (n : ℕ) :
    Sheaf.H (G X) n ≃+ Sheaf.H (G U) n := by
  let t : Scheme.Etale.mk e.hom ≅ T X := MorphismProperty.Over.isoMk e (by simp)
  let m := ((G X).cohomologyPresheaf n).mapIso t.op
  exact ((terminalHEquiv X (G X) n).symm.trans m.addCommGroupIsoToAddEquiv).trans
    (cohomologyOnOpenEquiv e.hom n)

theorem unitCohomologyIso_apply (e : U ≅ X) (n : ℕ) (a : Sheaf.H (G X) n) :
    unitCohomologyIso e n a = unitCohomologyPullback e.hom n a := rfl

end

end ManuscriptAudit.OpenEtaleUnitRestriction

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.OpenEtaleUnitRestriction.unitCohomologyIso_apply
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
