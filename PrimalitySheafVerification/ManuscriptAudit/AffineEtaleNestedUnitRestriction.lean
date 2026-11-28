import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NestedAffineEtaleHOneNaturality
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleRestrictedResolution

/-! The actual degree-one restriction with coefficients from the ambient
unit sheaf is bijective whenever the native affine unit restriction is. -/

namespace ManuscriptAudit.AffineEtaleNestedUnitRestriction

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open AffineEtaleOpenRestriction AffineEtaleRestrictedUnits AffineEtaleDerivedRestriction
open AffineEtaleTerminalExt NestedAffineEtaleRestriction NestedAffineEtaleHOneNaturality
open NestedOpenEtaleSectionNaturality OpenAffineEtaleHOneByRepresentatives KummerUnitsSheaf

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt
  KummerCohomologySequence.affineSiteHasExt

variable (A S : Type) [CommRing A] [CommRing S] [Algebra A S]

private abbrev X (R : Type) [CommRing R] := Spec (CommRingCat.of R)
private abbrev J (R : Type) [CommRing R] := Scheme.AffineEtale.topology (X R)
private abbrev i := Spec.map (CommRingCat.ofHom (algebraMap A S))
variable [IsOpenImmersion (i A S)]
variable {Y : Scheme.{0}} (j : X A ⟶ Y) [IsOpenImmersion j]

private abbrev G (R : Type) [CommRing R] := coordinateUnitSheaf (X R)
private abbrev F := fullCoordinateUnitSheaf Y
private abbrev L := restrictToAffine j
private abbrev R := affineRestriction (i A S)
private abbrev P := restrictToAffine (i A S ≫ j)
private abbrev e := nestedRestrictionIso (i A S) j

local instance : PreservesFiniteLimits (R A S) := (affineRestriction_exact (i A S)).1
local instance : PreservesFiniteColimits (R A S) := (affineRestriction_exact (i A S)).2
local instance : (R A S).Additive := (R A S).additive_of_preserves_binary_products

private def targetUnitsIso : (P A S j).obj (F (Y := Y)) ≅ G S :=
  ((e A S j).app (F (Y := Y))).symm ≪≫
    (R A S).mapIso (affineUnitsIso j) ≪≫ restrictionUnitsIso (i A S)

private theorem comparison (x : Sheaf.H ((L j).obj (F (Y := Y))) 1) :
    Sheaf.H.map (targetUnitsIso A S j).hom 1 (affineNestedHOne A S j (F (Y := Y)) x) =
    restrictHOne A S (Sheaf.H.map (affineUnitsIso j).hom 1 x) := by
  let z := Ext.mk₀ (restrictionConstant A S)
  let a := (affineUnitsIso j).hom
  let b := (restrictionUnitsIso (i A S)).hom
  let n := ((e A S j).app (F (Y := Y))).hom
  let t := (targetUnitsIso A S j).hom
  have ht : n ≫ t = (R A S).map a ≫ b := by
    simp [n, t, a, b, targetUnitsIso, Category.assoc]
  let x' := x.mapExactFunctor (R A S)
  change (z.comp (x'.comp (Ext.mk₀ n) (add_zero 1)) (zero_add 1)).comp (Ext.mk₀ t) (add_zero 1) =
    z.comp (((x.comp (Ext.mk₀ a) (add_zero 1)).mapExactFunctor (R A S)).comp (Ext.mk₀ b)
      (add_zero 1)) (zero_add 1)
  rw [Ext.comp_assoc_of_third_deg_zero z, Ext.comp_assoc_of_third_deg_zero x',
    ← Ext.mk₀_comp_mk₀, ht, Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_third_deg_zero x',
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]

/-- The coefficient comparison consists of actual isomorphisms, so the
derived restriction on the nested affine bases is an isomorphism. -/
theorem affineNestedHOne_bijective (h : Function.Bijective (restrictHOne A S)) :
    Function.Bijective (affineNestedHOne A S j (F (Y := Y))) := by
  let a := ((Sheaf.functorH (J A) 1).mapIso (affineUnitsIso j)).addCommGroupIsoToAddEquiv
  let b := ((Sheaf.functorH (J S) 1).mapIso (targetUnitsIso A S j)).addCommGroupIsoToAddEquiv
  have he (x) : b (affineNestedHOne A S j (F (Y := Y)) x) = restrictHOne A S (a x) :=
    comparison A S j x
  constructor
  · intro x y hxy
    apply a.injective
    apply h.1
    exact (he x).symm.trans ((congrArg b hxy).trans (he y))
  · intro y
    obtain ⟨x, hx⟩ := h.2 (b y)
    obtain ⟨w, rfl⟩ := a.surjective x
    exact ⟨w, b.injective ((he w).trans hx)⟩

/-- The genuine ambient first unit-cohomology presheaf arrow on the
literal nested opens is bijective when the native affine arrow is. -/
theorem ambientRestriction_bijective (h : Function.Bijective (restrictHOne A S)) :
    Function.Bijective
      (((F (Y := Y)).cohomologyPresheaf 1).map (nestedObjectArrow (i A S) j).op).hom := by
  letI : IsGrothendieckAbelian.{0} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{0}) := inferInstance
  letI : EnoughInjectives (Sheaf Y.smallEtaleTopology AddCommGrpCat.{0}) :=
    IsGrothendieckAbelian.enoughInjectives.{0} (C := Sheaf Y.smallEtaleTopology AddCommGrpCat.{0})
  let m := Injective.ι (F (Y := Y))
  let a := affineDegreeOneEquiv j m
  let b := affineDegreeOneEquiv (i A S ≫ j) m
  let r := (((F (Y := Y)).cohomologyPresheaf 1).map (nestedObjectArrow (i A S) j).op).hom
  let s := affineNestedHOne A S j (F (Y := Y))
  have he (x) : s (a x) = b (r x) := affineDegreeOneEquiv_nested A S j m x
  have hb := affineNestedHOne_bijective A S j h
  constructor
  · intro x y hxy
    apply a.injective
    apply hb.1
    rw [he, he, hxy]
  · intro y
    obtain ⟨x, hx⟩ := hb.2 (b y)
    obtain ⟨w, rfl⟩ := a.surjective x
    exact ⟨w, b.injective ((he w).symm.trans hx)⟩

end

end ManuscriptAudit.AffineEtaleNestedUnitRestriction

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleNestedUnitRestriction.affineNestedHOne_bijective,
      ``ManuscriptAudit.AffineEtaleNestedUnitRestriction.ambientRestriction_bijective] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
