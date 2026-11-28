import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NestedAffineEtaleSectionNaturality
import PrimalitySheafVerification.ManuscriptAudit.OpenAffineEtaleHOneByRepresentatives
import PrimalitySheafVerification.ManuscriptAudit.PreservedCokernelComposition
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleRestrictionNaturality

/-! Actual degree-one representatives commute with affine restriction along
nested ambient small étale opens. -/

namespace ManuscriptAudit.NestedAffineEtaleCokernelNaturality

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AffineEtaleTensorOverlap AffineEtaleOpenRestriction AffineEtaleOpenBaseChange
open AffineEtaleCechRestriction AffineEtaleRestrictionNaturality
open NestedAffineEtaleRestriction NestedAffineEtaleSectionNaturality
open NestedOpenEtaleSectionNaturality OpenAffineEtaleHOneByRepresentatives
open PreservedCokernelComposition

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

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

local instance : PreservesFiniteLimits (L A j) := (restrictToAffine_exact j).1
local instance : PreservesFiniteLimits (R A S) := (affineRestriction_exact (i A S)).1
local instance : PreservesFiniteLimits (P A S j) := (restrictToAffine_exact (i A S ≫ j)).1
local instance : PreservesFiniteColimits (L A j) := (restrictToAffine_exact j).2
local instance : PreservesFiniteColimits (R A S) := (affineRestriction_exact (i A S)).2
local instance : PreservesFiniteColimits (P A S j) := (restrictToAffine_exact (i A S ≫ j)).2
local instance : (L A j).Additive := (L A j).additive_of_preserves_binary_products
local instance : (R A S).Additive := (R A S).additive_of_preserves_binary_products
local instance : (P A S j).Additive := (P A S j).additive_of_preserves_binary_products

variable {F I : C (Y := Y)} (m : F ⟶ I) [Mono m]

/-- The literal restriction of an affine cokernel section before comparing
the source sheaf with the ambient restriction in one step. -/
def restrictedCokernelSection
    (x : (cokernel ((L A j).map m)).obj.obj (op (baseObject A))) :
    (cokernel ((R A S).map ((L A j).map m))).obj.obj (op (baseObject S)) :=
  (PreservesCokernel.iso (R A S) ((L A j).map m)).hom.hom.app (op (baseObject S))
    ((restrictSection (i A S) (cokernel ((L A j).map m)) (baseMap A S)).hom x)

/-- The actual ambient cokernel compared on the two affine bases sends the
actual restriction of a representative to the same cokernel section. -/
set_option maxHeartbeats 800000 in
theorem affineCokernelSections_nested (x : (cokernel m).obj.obj (op (Scheme.Etale.mk j))) :
    (inducedCokernelIso (L A j) (R A S) (P A S j) (e A S j) m).hom.hom.app (op (baseObject S))
      (restrictedCokernelSection A S j m (affineCokernelSections j m x)) =
    affineCokernelSections (i A S ≫ j) m
      ((cokernel m).obj.map (nestedObjectArrow (i A S) j).op x) := by
  let t := op (baseObject S)
  let q := PreservesCokernel.iso (L A j) m
  let q' := PreservesCokernel.iso (R A S) ((L A j).map m)
  let q'' := PreservesCokernel.iso (P A S j) m
  let k := inducedCokernelIso (L A j) (R A S) (P A S j) (e A S j) m
  let v := affineSectionEquiv j (cokernel m) x
  let w := (restrictSection (i A S) ((L A j).obj (cokernel m)) (baseMap A S)).hom v
  have hNatural := congrArg (fun f : ((L A j).obj (cokernel m)).obj.obj (op (baseObject A)) ⟶
      ((R A S).obj (cokernel ((L A j).map m))).obj.obj (op (baseObject S)) => f.hom v)
    (restrictSection_sheafMap (i A S) q.hom (baseMap A S))
  change (restrictSection (i A S) (cokernel ((L A j).map m)) (baseMap A S)).hom
      (q.hom.hom.app (op (baseObject A)) v) = ((R A S).map q.hom).hom.app t w at hNatural
  have hNested := affineSectionEquiv_nested A S j (cokernel m) x
  have hComp := congrArg (fun f : (R A S).obj ((L A j).obj (cokernel m)) ⟶
      cokernel ((P A S j).map m) => f.hom.app t w)
    (cokernelComparisons_compose (L A j) (R A S) (P A S j) (e A S j) m)
  change k.hom.hom.app t (q'.hom.hom.app t (((R A S).map q.hom).hom.app t w)) =
    q''.hom.hom.app t (((e A S j).hom.app (cokernel m)).hom.app t w) at hComp
  change k.hom.hom.app t (q'.hom.hom.app t
    ((restrictSection (i A S) (cokernel ((L A j).map m)) (baseMap A S)).hom
      (q.hom.hom.app (op (baseObject A)) v))) =
    q''.hom.hom.app t (affineSectionEquiv (i A S ≫ j) (cokernel m)
      ((cokernel m).obj.map (nestedObjectArrow (i A S) j).op x))
  rw [hNatural]
  exact hComp.trans (congrArg (fun y => q''.hom.hom.app t y) hNested)

end

end ManuscriptAudit.NestedAffineEtaleCokernelNaturality

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NestedAffineEtaleCokernelNaturality.affineCokernelSections_nested
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
