import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleDegreeOneComposition
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleUnitComparison

/-! The genuine degree-one étale unit-cohomology pullback respects
composition and actual commutative squares of open immersions. -/

namespace ManuscriptAudit.OpenEtaleUnitHOneComposition

open AlgebraicGeometry CategoryTheory Opposite
open OpenEtaleExtension OpenEtaleDegreeOneComposition KummerUnitsSheaf

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

private abbrev A := AddCommGrpCat.{0}
private abbrev G (X : Scheme.{0}) := fullCoordinateUnitSheaf X
private abbrev R {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j] := restriction j A
private abbrev u {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j] :=
  (OpenEtaleUnitComparison.restrictionIso j).hom

variable {V U X : Scheme.{0}}
variable (i : V ⟶ U) [IsOpenImmersion i] (j : U ⟶ X) [IsOpenImmersion j]

/-- The identification of actual unit sheaves is compatible with the
literal isomorphism of nested restrictions. -/
theorem restrictUnits_comp :
    (restrictionCompIso i j).inv.app (G X) ≫ (R i).map (u j) ≫ u i = u (i ≫ j) := by
  apply (sheafToPresheaf V.smallEtaleTopology A).map_injective
  apply NatTrans.ext
  funext T
  let e : etalePostcompose (i ≫ j) ≅ etalePostcompose i ⋙ etalePostcompose j :=
    MorphismProperty.Over.mapComp (P := @AlgebraicGeometry.Etale) ⊤
      (show Etale i from inferInstance) (show Etale j from inferInstance)
  change (fullCoordinateUnits X).map (e.inv.app T.unop).op ≫ 𝟙 _ ≫ 𝟙 _ = 𝟙 _
  change (Scheme.Γ ⋙ ringUnits).map (𝟙 T.unop.left).op ≫ 𝟙 _ ≫ 𝟙 _ = 𝟙 _
  simp

/-- Pullback of units in degree one on the actual small étale site. -/
def unitPullback : Sheaf.H (G X) 1 →+ Sheaf.H (G U) 1 :=
  pullbackWith j (u j)

/-- Genuine H¹ of the unit sheaf is contravariantly functorial for
the composite of the actual open immersions. -/
theorem unitPullback_comp (c : Sheaf.H (G X) 1) :
    unitPullback i (unitPullback j c) = unitPullback (i ≫ j) c := by
  change pullbackWith i (u i) (pullbackWith j (u j) c) = pullbackWith (i ≫ j) (u (i ≫ j)) c
  rw [pullbackWith_comp, restrictUnits_comp]

/-- Actual commutative squares induce commutative squares on H¹ of units. -/
theorem unitPullback_comm {Y : Scheme.{0}} (a : V ⟶ Y) [IsOpenImmersion a]
    (b : Y ⟶ X) [IsOpenImmersion b] (h : i ≫ j = a ≫ b) (c : Sheaf.H (G X) 1) :
    unitPullback i (unitPullback j c) = unitPullback a (unitPullback b c) := by
  rw [unitPullback_comp i j, unitPullback_comp a b, h]

end

end ManuscriptAudit.OpenEtaleUnitHOneComposition

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.OpenEtaleUnitHOneComposition.restrictUnits_comp,
      ``ManuscriptAudit.OpenEtaleUnitHOneComposition.unitPullback_comp,
      ``ManuscriptAudit.OpenEtaleUnitHOneComposition.unitPullback_comm] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
