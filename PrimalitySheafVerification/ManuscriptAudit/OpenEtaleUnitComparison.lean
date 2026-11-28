import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleCohomologyPresheaf
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleUnitSheaf
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleUnitCohomology

/-! Restricting actual coordinate units of an ambient small étale site
along an open immersion gives the actual coordinate-unit sheaf of that open. -/

namespace ManuscriptAudit.OpenEtaleUnitComparison

open AlgebraicGeometry CategoryTheory Opposite
open OpenEtaleExtension KummerUnitsSheaf

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt
  KummerCohomologySequence.affineSiteHasExt

private abbrev A := AddCommGrpCat.{0}

variable {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Restriction is the literal identification of units on the identical
underlying schemes of each small étale object. -/
def restrictionIso :
    (restriction j A).obj (fullCoordinateUnitSheaf X) ≅ fullCoordinateUnitSheaf U := by
  apply (fullyFaithfulSheafToPresheaf U.smallEtaleTopology A).preimageIso
  change (etalePostcompose j).op ⋙ fullCoordinateUnits X ≅ fullCoordinateUnits U
  refine NatIso.ofComponents (fun D => Iso.refl _) ?_
  intro D E f
  simp only [Iso.refl_hom, Category.id_comp, Category.comp_id] <;> rfl

/-- Values on an open of ambient unit-cohomology presheaves are actual
small étale coordinate-unit cohomology on that open. -/
def cohomologyEquiv (n : ℕ) :
    (fullCoordinateUnitSheaf X).H' n (Scheme.Etale.mk j) ≃+
      Sheaf.H (fullCoordinateUnitSheaf U) n :=
  (openCohomologyPresheafEquiv j (fullCoordinateUnitSheaf X) n).trans
    (((Sheaf.functorH U.smallEtaleTopology n).mapIso (restrictionIso j)).addCommGroupIsoToAddEquiv)

/-- At an affine open the same ambient presheaf values compute ordinary
unit cohomology on the affine basis. -/
def affineCohomologyEquiv (R : CommRingCat.{0})
    (f : Spec R ⟶ X) [IsOpenImmersion f] (n : ℕ) :
    (fullCoordinateUnitSheaf X).H' n (Scheme.Etale.mk f) ≃+
      Sheaf.H (coordinateUnitSheaf (Spec R)) n := by
  let e := ((Sheaf.functorH (Scheme.AffineEtale.topology (Spec R)) n).mapIso
    (coordinateUnitSheafIso (Spec R))).addCommGroupIsoToAddEquiv
  exact (cohomologyEquiv f n).trans ((unitCohomologyEquiv R n).symm.trans e.symm)

end

end ManuscriptAudit.OpenEtaleUnitComparison

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.OpenEtaleUnitComparison.restrictionIso,
      ``ManuscriptAudit.OpenEtaleUnitComparison.cohomologyEquiv,
      ``ManuscriptAudit.OpenEtaleUnitComparison.affineCohomologyEquiv] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
