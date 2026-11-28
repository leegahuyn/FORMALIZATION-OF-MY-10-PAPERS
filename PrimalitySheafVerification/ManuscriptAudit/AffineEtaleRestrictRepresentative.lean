import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleOpenBaseChange
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleRestrictionNaturality
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleRestrictedResolution
import PrimalitySheafVerification.ManuscriptAudit.AffineEtalePicardSameCover

/-! The actual local lift representing degree-one unit cohomology pulls
back along an open and yields the actual pulled unit cocycle. -/

namespace ManuscriptAudit.AffineEtaleRestrictRepresentative

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AffineEtaleTensorOverlap AffineEtaleOpenRestriction AffineEtaleOpenBaseChange
open AffineEtaleCechRestriction AffineEtaleRestrictionNaturality
open AffineEtaleRestrictedUnits AffineEtaleRestrictedResolution
open AffineEtalePicardSameCover AffineEtaleUnitCocycle SheafSectionDifference
open FlatTwistedBaseChangeLine TwistedTensorEqualizer KummerUnitsSheaf

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] doubleEtale

variable (A B S : Type) [CommRing A] [CommRing B] [CommRing S]
variable [Algebra A B] [Algebra A S] [Algebra.Etale A B] [Algebra.Etale S (Cover A B S)]

private abbrev X (R : Type) [CommRing R] := Spec (CommRingCat.of R)
private abbrev j := Spec.map (CommRingCat.ofHom (algebraMap A S))
variable [IsOpenImmersion (j A S)]

private abbrev C (R : Type) [CommRing R] := Sheaf (Scheme.AffineEtale.topology (X R)) AddCommGrpCat.{0}
private abbrev G (R : Type) [CommRing R] := coordinateUnitSheaf (X R)
private abbrev R := affineRestriction (j A S)

variable {I : C A} (i : G A ⟶ I) [Mono i]
private abbrev i' := restrictedInjection (j A S) i

/-- The restricted global section of the actual cokernel sheaf. -/
def restrictGlobal (x : (cokernel i).obj.obj (op (baseObject A))) :
    (cokernel (i' A S i)).obj.obj (op (baseObject S)) :=
  ((restrictedCokernelIso (j A S) i).hom.hom.app (op (baseObject S))).hom
    ((restrictSection (j A S) (cokernel i) (baseMap A S)).hom x)

/-- The local lift on the actual base-changed cover. -/
def restrictLift (y : I.obj.obj (op (ofAlgebra A B))) :
    ((R A S).obj I).obj.obj (op (ofAlgebra S (Cover A B S))) :=
  (restrictSection (j A S) I (coverMap A B S)).hom y

variable (x : (cokernel i).obj.obj (op (baseObject A)))
variable (y : I.obj.obj (op (ofAlgebra A B)))
variable (hy : (cokernel.π i).hom.app (op (ofAlgebra A B)) y =
  (cokernel i).obj.map (coverArrow A B).op x)

/-- The restricted lift has the genuine restricted global class as image. -/
theorem restrictLift_spec :
    (cokernel.π (i' A S i)).hom.app (op (ofAlgebra S (Cover A B S))) (restrictLift A B S y) =
      (cokernel (i' A S i)).obj.map (coverArrow S (Cover A B S)).op
        (restrictGlobal A S i x) := by
  let D := ofAlgebra S (Cover A B S)
  let E := baseObject S
  let q := restrictedCokernelIso (j A S) i
  let r := coverMap A B S
  let s := baseMap A S
  let a := coverArrow S (Cover A B S)
  have hRep :
      (restrictSection (j A S) I r) ≫ (cokernel.π (i' A S i)).hom.app (op D) =
      (cokernel.π i).hom.app (op (ofAlgebra A B)) ≫
        restrictSection (j A S) (cokernel i) r ≫ q.hom.hom.app (op D) := by
    rw [← Category.assoc ((cokernel.π i).hom.app (op (ofAlgebra A B))),
      restrictSection_sheafMap, Category.assoc]
    congr 1
    have h := restrictedCokernel_projection (j A S) i
    exact (congrArg (fun f : (R A S).obj I ⟶ cokernel (i' A S i) =>
      f.hom.app (op D)) h).symm
  have hCov :
      (cokernel i).obj.map (coverArrow A B).op ≫ restrictSection (j A S) (cokernel i) r =
        restrictSection (j A S) (cokernel i) s ≫ ((R A S).obj (cokernel i)).obj.map a.op := by
    rw [restrictSection_source, restrictSection_target, coverSquare]
  have h₁ := congrArg (fun f => f.hom y) hRep
  have h₂ := congrArg (fun f => f.hom x) hCov
  unfold restrictGlobal restrictLift
  simp only [ConcreteCategory.comp_apply] at h₁ h₂
  rw [h₁, hy, h₂]
  exact (NatTrans.naturality_apply q.hom.hom a.op ((restrictSection (j A S) (cokernel i) s).hom x))

/-- The transition of the restricted actual representative is the pullback
of the original transition through the genuine double-overlap homomorphism. -/
theorem restrictLift_transition :
    transition S (Cover A B S) (i' A S i) (restrictGlobal A S i x) (restrictLift A B S y)
        (restrictLift_spec A B S i x y hy) =
      pulledUnit A B S (transition A B i x y hy) := by
  let D := ofAlgebra S (Double S (Cover A B S))
  let W := ofAlgebra A (Double A B)
  let q := doubleMap A B S
  let v : Additive (Double A B)ˣ := Additive.ofMul (transition A B i x y hy)
  have hUnit := restrictionUnits_section (j A S) q v
  have hUnits :
      ((restrictionUnitsIso (j A S)).hom.hom.app (op D)).hom
        ((restrictSection (j A S) (G A) q).hom v) =
      Additive.ofMul (pulledUnit A B S (transition A B i x y hy)) := hUnit
  apply (Additive.ofMul (α := (Double S (Cover A B S))ˣ)).injective
  apply section_injective (i' A S i) D
  rw [transition_image, ← hUnits]
  have hm := restrictSection_sheafMap (j A S) i q
  have ht := congrArg (fun f => f.hom v) hm
  simp only [ConcreteCategory.comp_apply] at ht
  change _ = ((R A S).map i).hom.app (op D)
      ((restrictSection (j A S) (G A) q).hom v) at ht
  have hv : (i' A S i).hom.app (op D)
      (((restrictionUnitsIso (j A S)).hom.hom.app (op D)).hom
        ((restrictSection (j A S) (G A) q).hom v)) =
      ((R A S).map i).hom.app (op D)
        ((restrictSection (j A S) (G A) q).hom v) := by
    have h : (restrictionUnitsIso (j A S)).hom ≫ i' A S i = (R A S).map i := by
      simp [restrictedInjection]
    exact congrArg (fun f : (R A S).obj (G A) ⟶ (R A S).obj I =>
      f.hom.app (op D) ((restrictSection (j A S) (G A) q).hom v)) h
  rw [hv, ← ht]
  have hDiff := restrictSection_difference (j A S) I (coverMap A B S) q
    (firstProjection S (Cover A B S)) (secondProjection S (Cover A B S))
    (firstProjection A B) (secondProjection A B) (firstSquare A B S) (secondSquare A B S) y
  have hImage : i.hom.app (op W) v =
      I.obj.map (firstProjection A B).op y - I.obj.map (secondProjection A B).op y :=
    transition_image A B i x y hy
  rw [hImage]
  exact hDiff.symm

end

end ManuscriptAudit.AffineEtaleRestrictRepresentative

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleRestrictRepresentative.restrictLift_spec,
      ``ManuscriptAudit.AffineEtaleRestrictRepresentative.restrictLift_transition] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
