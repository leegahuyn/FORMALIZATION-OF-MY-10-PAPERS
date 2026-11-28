import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleTerminalExt
import PrimalitySheafVerification.ManuscriptAudit.NestedAffineEtaleCokernelNaturality
import PrimalitySheafVerification.ManuscriptAudit.ConnectingExtNaturality

/-! The first cohomology restriction on two genuine affine opens is the
actual ambient small étale cohomology presheaf restriction. -/

namespace ManuscriptAudit.NestedAffineEtaleHOneNaturality

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open AffineEtaleTensorOverlap AffineEtaleOpenRestriction AffineEtaleOpenBaseChange
open AffineEtaleCechRestriction AffineEtaleDerivedRestriction AffineEtaleTerminalExt
open NestedAffineEtaleRestriction NestedAffineEtaleCokernelNaturality
open NestedOpenEtaleSectionNaturality OpenAffineEtaleHOneByRepresentatives
open PreservedCokernelComposition EtalePresheafHOneRepresentatives SheafH1Descent

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt
  KummerCohomologySequence.affineSiteHasExt

variable (A S : Type) [CommRing A] [CommRing S] [Algebra A S]

private abbrev X (R : Type) [CommRing R] := Spec (CommRingCat.of R)
private abbrev i := Spec.map (CommRingCat.ofHom (algebraMap A S))
variable [IsOpenImmersion (i A S)]
variable {Y : Scheme.{0}} (j : X A ⟶ Y) [IsOpenImmersion j]

private abbrev C := Sheaf Y.smallEtaleTopology AddCommGrpCat.{0}
private abbrev L := restrictToAffine j
private abbrev R := affineRestriction (i A S)
private abbrev P := restrictToAffine (i A S ≫ j)
private abbrev e := nestedRestrictionIso (i A S) j
private abbrev terminal (B : Type) [CommRing B] :=
  KummerAffineCohomology.affineTerminal_isTerminal (CommRingCat.of B)

local instance : PreservesFiniteLimits (L j) := (restrictToAffine_exact j).1
local instance : PreservesFiniteLimits (R A S) := (affineRestriction_exact (i A S)).1
local instance : PreservesFiniteLimits (P A S j) := (restrictToAffine_exact (i A S ≫ j)).1
local instance : PreservesFiniteColimits (L j) := (restrictToAffine_exact j).2
local instance : PreservesFiniteColimits (R A S) := (affineRestriction_exact (i A S)).2
local instance : PreservesFiniteColimits (P A S j) := (restrictToAffine_exact (i A S ≫ j)).2
local instance : (L j).Additive := (L j).additive_of_preserves_binary_products
local instance : (R A S).Additive := (R A S).additive_of_preserves_binary_products
local instance : (P A S j).Additive := (P A S j).additive_of_preserves_binary_products

/-- Degree-one affine restriction with the exact comparison to the
ambient sheaf already restricted onto the overlap. -/
def affineNestedHOne (F : C (Y := Y)) :
    Sheaf.H ((L j).obj F) 1 →+ Sheaf.H ((P A S j).obj F) 1 :=
  ((Ext.mk₀ (restrictionConstant A S)).precomp _ (zero_add 1)).comp
    (((Ext.mk₀ ((e A S j).app F).hom).postcomp _ (add_zero 1)).comp
      ((R A S).mapExtAddHom (constantInteger A) ((L j).obj F) 1))

private abbrev seq {D : Type*} [Category* D] [Abelian D]
    {F I : D} (f : F ⟶ I) :=
  ShortComplex.mk f (cokernel.π f) (cokernel.condition f)

private theorem short_exact {D : Type*} [Category* D] [Abelian D]
    {F I : D} (f : F ⟶ I) [Mono f] : (seq f).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f)
  mono_f := inferInstance
  epi_g := inferInstance

variable {F I : C (Y := Y)} (m : F ⟶ I) [Mono m]

private abbrev induced := inducedCokernelIso (L j) (R A S) (P A S j) (e A S j) m
private abbrev cokernelComparison :=
  (PreservesCokernel.iso (R A S) ((L j).map m)).hom ≫ (induced A S j m).hom

private def sequenceComparison :
    (seq ((L j).map m)).map (R A S) ⟶ seq ((P A S j).map m) where
  τ₁ := ((e A S j).app F).hom
  τ₂ := ((e A S j).app I).hom
  τ₃ := cokernelComparison A S j m
  comm₁₂ := ((e A S j).hom.naturality m).symm
  comm₂₃ := by
    change ((e A S j).app I).hom ≫ cokernel.π ((P A S j).map m) =
      (R A S).map (cokernel.π ((L j).map m)) ≫ cokernelComparison A S j m
    unfold cokernelComparison
    rw [← Category.assoc, PreservesCokernel.π_iso_hom]
    simp [induced, inducedCokernelIso, cokernel.mapIso]

/-- The affine derived map sends an actual connecting representative to
the connecting representative of the actual restricted section. -/
theorem affineNestedHOne_connecting
    (x : (cokernel ((L j).map m)).obj.obj (op (baseObject A))) :
    affineNestedHOne A S j F (connectingSection ((L j).map m) (terminal A) x) =
      connectingSection ((P A S j).map m) (terminal S)
        ((induced A S j m).hom.hom.app (op (baseObject S))
          (restrictedCokernelSection A S j m x)) := by
  let a := (L j).map m
  let b := (P A S j).map m
  let q := sequenceComparison A S j m
  let g := cokernelComparison A S j m
  let z : (cokernel b).obj.obj (op (baseObject S)) :=
    (induced A S j m).hom.hom.app (op (baseObject S)) (restrictedCokernelSection A S j m x)
  have hz := sectionHom_restrict A S g x
  change sectionHom S (cokernel b) z =
    restrictionConstant A S ≫ (R A S).map (sectionHom A (cokernel a) x) ≫ g at hz
  have h := ConnectingExtNaturality.map_connecting (R A S)
    (short_exact a) (short_exact b) q (restrictionConstant A S) (sectionHom A (cokernel a) x)
  change (Ext.mk₀ (restrictionConstant A S)).comp
      ((((Ext.mk₀ (sectionHom A (cokernel a) x)).comp (short_exact a).extClass (zero_add 1)).
        mapExactFunctor (R A S)).comp (Ext.mk₀ ((e A S j).app F).hom)
          (add_zero 1)) (zero_add 1) =
    (Ext.mk₀ (restrictionConstant A S ≫ (R A S).map (sectionHom A (cokernel a) x) ≫
      g)).comp (short_exact b).extClass (zero_add 1) at h
  rw [← hz, mk₀_sectionHom, mk₀_sectionHom] at h
  exact h

variable [Injective I]

/-- Actual ambient degree-one restriction on the small étale site agrees
with derived restriction on the two literal affine bases. -/
theorem affineDegreeOneEquiv_nested (c : F.H' 1 (Scheme.Etale.mk j)) :
    affineNestedHOne A S j F (affineDegreeOneEquiv j m c) =
    affineDegreeOneEquiv (i A S ≫ j) m
      ((F.cohomologyPresheaf 1).map (nestedObjectArrow (i A S) j).op c) := by
  obtain ⟨x, rfl⟩ := connectingAt_surjective m (Scheme.Etale.mk j) c
  rw [connectingAt_natural, affineDegreeOneEquiv_connecting,
    affineDegreeOneEquiv_connecting, affineNestedHOne_connecting, affineCokernelSections_nested]

end

end ManuscriptAudit.NestedAffineEtaleHOneNaturality

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NestedAffineEtaleHOneNaturality.affineNestedHOne_connecting,
      ``ManuscriptAudit.NestedAffineEtaleHOneNaturality.affineDegreeOneEquiv_nested] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
