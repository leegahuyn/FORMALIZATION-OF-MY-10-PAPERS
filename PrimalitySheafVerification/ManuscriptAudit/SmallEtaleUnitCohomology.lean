import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.KummerCohomologyDegreeTwo
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleUnitSheaf

/-!
# Derived cohomology of the full small étale unit sheaf

The affine coordinate-unit sheaf is the restriction of the actual full
unit sheaf. The same derived cohomology comparison used for constants
therefore also applies to units. In degree two the Kummer obstruction
can be expressed entirely on the full small étale site.
-/

namespace ManuscriptAudit.KummerUnitsSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian Opposite
open KummerSheafSequence KummerCohomologyDegreeTwo

noncomputable section

set_option backward.isDefEq.respectTransparency false

attribute [local instance] KummerCohomologySequence.affineSiteHasExt
  SmallEtaleCohomologyComparison.fullSiteHasExt

private abbrev affineSite (R : CommRingCat.{0}) := Scheme.AffineEtale.topology (Spec R)
private abbrev fullSite (R : CommRingCat.{0}) := (Spec R).smallEtaleTopology
private abbrev E (R : CommRingCat.{0}) := Scheme.AffineEtale.sheafEquiv (Spec R) AddCommGrpCat.{0}

/-- The actual restriction of the full unit sheaf is the affine unit sheaf. -/
def affineUnitRestrictionIso (R : CommRingCat.{0}) :
    (E R).inverse.obj (fullCoordinateUnitSheaf (Spec R)) ≅ unitSheaf (Spec R) := by
  let F := (E R).inverse.obj (fullCoordinateUnitSheaf (Spec R))
  let G := coordinateUnitSheaf (Spec R)
  have e : F.obj ≅ G.obj := by
    change (Scheme.AffineEtale.Spec (Spec R)).op ⋙ fullCoordinateUnits (Spec R) ≅
      KummerUnitsPresheaf.units (Spec R)
    exact affineRestrictionUnitsIso (Spec R)
  let e' : F ≅ G := (fullyFaithfulSheafToPresheaf (affineSite R) AddCommGrpCat.{0}).preimageIso e
  exact e' ≪≫ coordinateUnitSheafIso (Spec R)

/-- The actual small affine and full étale unit cohomology groups agree in every degree. -/
def unitCohomologyEquiv (R : CommRingCat.{0}) (n : ℕ) :
    Sheaf.H (unitSheaf (Spec R)) n ≃+ Sheaf.H (fullCoordinateUnitSheaf (Spec R)) n := by
  let C := Sheaf (affineSite R) AddCommGrpCat.{0}
  letI : IsGrothendieckAbelian.{0} C :=
    Scheme.isGrothendieckAbelian_sheaf_affineEtaleTopology (Spec R) AddCommGrpCat.{0}
  letI : EnoughInjectives C := IsGrothendieckAbelian.enoughInjectives.{0} (C := C)
  let F := (E R).functor
  letI : F.Additive := F.additive_of_preserves_binary_products
  let Z := AddCommGrpCat.of (ULift.{0} ℤ)
  let X := (constantSheaf (affineSite R) AddCommGrpCat.{0}).obj Z
  let Y := unitSheaf (Spec R)
  let e₀ := AddEquiv.ofBijective (F.mapExtAddHom X Y n)
    (F.mapExt_bijective_of_preservesInjectiveObjects X Y n)
  let e₁ := (((extFunctor (C := Sheaf (fullSite R) AddCommGrpCat.{0}) n).mapIso
    ((SmallEtaleCohomologyComparison.constantComparison R).app Z).symm.op).app
      (F.obj Y)).addCommGroupIsoToAddEquiv
  let eY : F.obj Y ≅ fullCoordinateUnitSheaf (Spec R) :=
    F.mapIso (affineUnitRestrictionIso R).symm ≪≫ (E R).counitIso.app _
  let e₂ := ((Sheaf.functorH (fullSite R) n).mapIso eY).addCommGroupIsoToAddEquiv
  exact e₀.trans (e₁.trans e₂)

/-- Unit cohomology in degree one vanishes on the full site of a PID,
including on the spectrum of any field. -/
theorem unitHOne_subsingleton_of_pid (R : Type) [CommRing R]
    [IsDomain R] [IsPrincipalIdealRing R] :
    Subsingleton (Sheaf.H (fullCoordinateUnitSheaf (Spec (CommRingCat.of R))) 1) := by
  let e := unitCohomologyEquiv (CommRingCat.of R) 1
  have h := AffineEtaleCuspHOne.unitSheaf_HOne_subsingleton_of_pid R
  exact ⟨fun x y => e.symm.injective (h.allEq (e.symm x) (e.symm y))⟩

private def killedByEquiv {U V : Type} [AddCommGroup U] [AddCommGroup V]
    (e : U ≃+ V) (d : ℕ) : killedBy U d ≃+ killedBy V d where
  toFun u := ⟨e u.val, by
    change d • e u.val = 0
    rw [← map_nsmul, show d • u.val = 0 from u.property, map_zero]⟩
  invFun v := ⟨e.symm v.val, by
    change d • e.symm v.val = 0
    rw [← map_nsmul, show d • v.val = 0 from v.property, map_zero]⟩
  left_inv u := Subtype.ext (e.symm_apply_apply u.val)
  right_inv v := Subtype.ext (e.apply_symm_apply v.val)
  map_add' u v := Subtype.ext (e.map_add u.val v.val)

/-- On the affine line, degree-two cohomology with cyclic coefficients is
the torsion subgroup of degree-two cohomology of the full unit sheaf. -/
def affineLineCyclicHTwoFullUnitsEquiv (K : Type) [Field K] [IsAlgClosed K]
    (d : ℕ) [NeZero (d : K)] :
    Sheaf.H ((constantSheaf (Spec (CommRingCat.of (Polynomial K))).smallEtaleTopology
      AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ZMod d))) 2 ≃+
    killedBy (Sheaf.H (fullCoordinateUnitSheaf (Spec (CommRingCat.of (Polynomial K)))) 2) d :=
  (affineLineCyclicHTwoEquiv K d).trans
    (killedByEquiv (unitCohomologyEquiv (CommRingCat.of (Polynomial K)) 2) d)

end

end ManuscriptAudit.KummerUnitsSheaf

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.KummerUnitsSheaf.affineUnitRestrictionIso,
      ``ManuscriptAudit.KummerUnitsSheaf.unitCohomologyEquiv,
      ``ManuscriptAudit.KummerUnitsSheaf.unitHOne_subsingleton_of_pid,
      ``ManuscriptAudit.KummerUnitsSheaf.affineLineCyclicHTwoFullUnitsEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
