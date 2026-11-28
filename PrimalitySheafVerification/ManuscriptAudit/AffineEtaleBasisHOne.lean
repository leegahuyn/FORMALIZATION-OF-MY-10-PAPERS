import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
import PrimalitySheafVerification.ManuscriptAudit.ExtOneFunctoriality
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleConstantRestrictionSquare
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleDegreeOneExt

/-! The actual degree-one étale cohomology of an affine scheme and its
actual affine basis compare naturally under the genuine restriction functors. -/

namespace ManuscriptAudit.AffineEtaleBasisHOne

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open AffineEtaleOpenRestriction OpenEtaleExtension OpenEtaleDegreeOneExt
open TerminalCohomologySectionHom AffineEtaleTerminalBasisSectionHom
open AffineEtaleConstantRestrictionSquare OpenEtaleTerminalSectionHom ExtOneFunctoriality

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt
  KummerCohomologySequence.affineSiteHasExt

private abbrev B := AddCommGrpCat.{0}
private abbrev X (A : Type) [CommRing A] := Spec (CommRingCat.of A)
private abbrev C (A : Type) [CommRing A] := Sheaf (X A).smallEtaleTopology B
private abbrev Jb (A : Type) [CommRing A] := Scheme.AffineEtale.topology (X A)
private abbrev Cb (A : Type) [CommRing A] := Sheaf (Jb A) B
private abbrev E (A : Type) [CommRing A] := Scheme.AffineEtale.sheafEquiv (X A) B
private abbrev Z (A : Type) [CommRing A] := integerSheaf (X A).smallEtaleTopology
private abbrev Zb (A : Type) [CommRing A] := integerSheaf (Jb A)

variable (A : Type) [CommRing A]

local instance : (E A).inverse.Additive := (E A).inverse.additive_of_preserves_binary_products

/-- Actual derived comparison from the full small site to the affine basis. -/
def basisHOneMap (P : C A) : Sheaf.H P 1 →+ Sheaf.H ((E A).inverse.obj P) 1 :=
  ((Ext.mk₀ (basisIntegerIso A).hom).precomp _ (zero_add 1)).comp
    ((E A).inverse.mapExtAddHom (Z A) P 1)

theorem basisHOneMap_bijective (P : C A) : Function.Bijective (basisHOneMap A P) := by
  letI : (E A).inverse.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms (E A).toAdjunction
  let e := (((extFunctor (C := Cb A) 1).mapIso (basisIntegerIso A).op).app
    ((E A).inverse.obj P)).addCommGroupIsoToAddEquiv
  exact e.bijective.comp
    ((E A).inverse.mapExt_bijective_of_preservesInjectiveObjects (Z A) P 1)


/-- The actual basis comparison is natural in each coefficient morphism. -/
theorem basisHOneMap_coeff {P Q : C A} (f : P ⟶ Q) (x : Sheaf.H P 1) :
    basisHOneMap A Q (Sheaf.H.map f 1 x) =
      Sheaf.H.map ((E A).inverse.map f) 1 (basisHOneMap A P x) := by
  let b := Ext.mk₀ (basisIntegerIso A).hom
  let E' := (E A).inverse
  change b.comp ((x.comp (Ext.mk₀ f) (add_zero 1)).mapExactFunctor E') (zero_add 1) =
    (b.comp (x.mapExactFunctor E') (zero_add 1)).comp (Ext.mk₀ (E'.map f)) (add_zero 1)
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.comp_assoc_of_third_deg_zero]

variable (S : Type) [CommRing S] [Algebra A S]

private abbrev i := Spec.map (CommRingCat.ofHom (algebraMap A S))
variable [IsOpenImmersion (i A S)]
private abbrev F := restriction (i A S) B
private abbrev R := affineRestriction (i A S)
private abbrev e := siteSquare A S

local instance : PreservesFiniteLimits (F A S) := (restriction_exact (i A S)).1
local instance : PreservesFiniteColimits (F A S) := (restriction_exact (i A S)).2
local instance : (F A S).Additive := restriction_additive (i A S)
local instance : PreservesFiniteLimits (R A S) := (affineRestriction_exact (i A S)).1
local instance : PreservesFiniteColimits (R A S) := (affineRestriction_exact (i A S)).2
local instance : (R A S).Additive := (R A S).additive_of_preserves_binary_products

/-- Native affine-basis degree-one restriction with its actual integer source. -/
def affineExtPullback (P : Cb A) : Sheaf.H P 1 →+ Sheaf.H ((R A S).obj P) 1 :=
  ((Ext.mk₀ (AffineEtaleDerivedRestriction.restrictionConstant A S)).precomp _ (zero_add 1)).comp
    ((R A S).mapExtAddHom (Zb A) P 1)


/-- Actual affine-basis restriction is natural in its coefficients. -/
theorem affineExtPullback_coeff {P Q : Cb A} (f : P ⟶ Q) (x : Sheaf.H P 1) :
    affineExtPullback A S Q (Sheaf.H.map f 1 x) =
      Sheaf.H.map ((R A S).map f) 1 (affineExtPullback A S P x) := by
  let b := Ext.mk₀ (AffineEtaleDerivedRestriction.restrictionConstant A S)
  let E' := R A S
  change b.comp ((x.comp (Ext.mk₀ f) (add_zero 1)).mapExactFunctor E') (zero_add 1) =
    (b.comp (x.mapExactFunctor E') (zero_add 1)).comp (Ext.mk₀ (E'.map f)) (add_zero 1)
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.comp_assoc_of_third_deg_zero]

/-- The actual full and affine derived restrictions agree in degree one. -/
theorem basisHOne_square (P : C A) (x : Sheaf.H P 1) :
    Sheaf.H.map ((e A S).hom.app P) 1
      (affineExtPullback A S ((E A).inverse.obj P) (basisHOneMap A P x)) =
    basisHOneMap S ((F A S).obj P) (extPullback (i A S) P x) := by
  let a := (basisIntegerIso A).hom
  let b := AffineEtaleDerivedRestriction.restrictionConstant A S
  let c := (constantIntegerIso (i A S)).hom
  let d := (basisIntegerIso S).hom
  let e' := (e A S).hom
  let x₁ := x.mapExactFunctor (E A).inverse
  let x₂ := x.mapExactFunctor (F A S)
  let u := b ≫ (R A S).map a
  let v := d ≫ (E S).inverse.map c
  have h : u ≫ e'.app (Z A) = v := by
    change (b ≫ (R A S).map a) ≫ e'.app (Z A) = v
    rw [Category.assoc]
    exact integer_square A S
  change ((Ext.mk₀ b).comp (((Ext.mk₀ a).comp x₁ (zero_add 1)).mapExactFunctor (R A S))
      (zero_add 1)).comp (Ext.mk₀ (e'.app P)) (add_zero 1) =
    (Ext.mk₀ d).comp (((Ext.mk₀ c).comp x₂ (zero_add 1)).mapExactFunctor (E S).inverse) (zero_add 1)
  simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀_assoc]
  change ((Ext.mk₀ u).comp (x₁.mapExactFunctor (R A S)) (zero_add 1)).comp
      (Ext.mk₀ (e'.app P)) (add_zero 1) =
    (Ext.mk₀ v).comp (x₂.mapExactFunctor (E S).inverse) (zero_add 1)
  have h₁ := map_comp_functor (E A).inverse (R A S) x
  have h₂ := map_comp_functor (F A S) (E S).inverse x
  change x₁.mapExactFunctor (R A S) = _ at h₁
  change x₂.mapExactFunctor (E S).inverse = _ at h₂
  rw [h₁, h₂]
  exact precomp_natural (F A S ⋙ (E S).inverse) e' u v h x

end

end ManuscriptAudit.AffineEtaleBasisHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleBasisHOne.basisHOneMap_bijective,
      ``ManuscriptAudit.AffineEtaleBasisHOne.basisHOne_square] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
