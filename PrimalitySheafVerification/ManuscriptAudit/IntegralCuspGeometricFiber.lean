import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineCuspSmoothPuncture
import PrimalitySheafVerification.ManuscriptAudit.CuspProperCompactification
import PrimalitySheafVerification.ManuscriptAudit.IntegralNodalGeometricFiber

/-! The fixed integral cusp, its geometric fibres, and their actual relative smooth opens. -/

namespace ManuscriptAudit.IntegralCuspGeometricFiber

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open IntegralOddPrimeFibers (cuspToResidue)
open IntegralNodalGeometricFiber (closureField geometricResidueMap)
open IntPrimeResidueFiber (closedPoint residueSpecIso_over)
open IntegralCuspNodalAffine (cuspToInt cuspFiberIso cuspFiberIso_over)
open CuspProperCompactification (affineCusp affineOpen projectiveCusp)
open SmallEtaleGeometricBaseChange (cuspPuncturedOpen)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (p : ℕ) [Fact p.Prime]

private abbrev base := Spec (CommRingCat.of ℤ)
private abbrev residueToBase := base.fromSpecResidueField (closedPoint p)

/-- The geometric cusp fibre is the pullback of the actual arithmetic fibre at (p). -/
abbrev geometricFiber := pullback (geometricResidueMap p) (cuspToResidue p)

def geometricToBase : geometricFiber p ⟶ Spec (CommRingCat.of (closureField p)) :=
  pullback.fst _ _

instance geometric_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (geometricToBase p) :=
  inferInstanceAs (LocallyOfFinitePresentation (pullback.fst (geometricResidueMap p) (cuspToResidue p)))

private theorem geometricResidue_over :
    geometricResidueMap p ≫ residueToBase p = IntegralCuspNodalAffine.coefficientPoint (closureField p) := by
  rw [geometricResidueMap, Category.assoc, residueSpecIso_over]
  change Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (closureField p))) ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℤ (ZMod p))) = _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact (IsScalarTower.algebraMap_eq ℤ (ZMod p) (closureField p)).symm

private def toIntegralFiber :
    geometricFiber p ≅ IntegralCuspArithmeticBump.fiber (closureField p) :=
  pullbackRightPullbackFstIso (residueToBase p) cuspToInt (geometricResidueMap p) ≪≫
    pullback.congrHom (geometricResidue_over p) rfl

private theorem toIntegralFiber_over :
    (toIntegralFiber p).hom ≫ IntegralCuspArithmeticBump.fiberToBase (closureField p) =
      geometricToBase p := by
  change ((pullbackRightPullbackFstIso (residueToBase p) cuspToInt (geometricResidueMap p)).hom ≫
    (pullback.congrHom (geometricResidue_over p) (rfl : cuspToInt = cuspToInt)).hom) ≫
      pullback.fst (IntegralCuspNodalAffine.coefficientPoint (closureField p)) cuspToInt =
    pullback.fst (geometricResidueMap p) (cuspToResidue p)
  rw [Category.assoc]
  have h := pullbackRightPullbackFstIso_hom_fst (residueToBase p) cuspToInt (geometricResidueMap p)
  simpa only [pullback.congrHom, asIso_hom, pullback.map, pullback.lift_fst, Category.comp_id,
    cuspToResidue] using h

/-- The geometric fibre is identified with the actual affine cusp over the algebraic closure. -/
def affineIso : geometricFiber p ≅ affineCusp (closureField p) :=
  toIntegralFiber p ≪≫ cuspFiberIso (closureField p)

theorem affineIso_over :
    (affineIso p).hom ≫ AffineCuspSmoothLocus.cuspToBase (closureField p) = geometricToBase p := by
  change ((toIntegralFiber p).hom ≫ (cuspFiberIso (closureField p)).hom) ≫ _ = _
  rw [Category.assoc]
  have h : (cuspFiberIso (closureField p)).hom ≫
      AffineCuspSmoothLocus.cuspToBase (closureField p) =
        IntegralCuspArithmeticBump.fiberToBase (closureField p) :=
    cuspFiberIso_over (closureField p)
  rw [h, toIntegralFiber_over]

abbrev geometricSmoothOpen := (geometricToBase p).smoothLocus

private def toModelSmooth :
    (geometricSmoothOpen p).toScheme ≅
      (AffineCuspSmoothLocus.cuspToBase (closureField p)).smoothLocus.toScheme :=
  SmoothLocusUnderIso.iso (affineIso p) (geometricToBase p)
    (AffineCuspSmoothLocus.cuspToBase (closureField p)) (affineIso_over p)

private theorem toModelSmooth_fac :
    (toModelSmooth p).hom ≫ (AffineCuspSmoothLocus.cuspToBase (closureField p)).smoothLocus.ι =
      (geometricSmoothOpen p).ι ≫ (affineIso p).hom := by
  unfold toModelSmooth SmoothLocusUnderIso.iso
  exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

private def modelPunctureIso :
    (AffineCuspSmoothLocus.cuspToBase (closureField p)).smoothLocus.toScheme ≅
      (cuspPuncturedOpen (closureField p)).toScheme :=
  IsOpenImmersion.isoOfRangeEq (AffineCuspSmoothLocus.cuspToBase (closureField p)).smoothLocus.ι
    (cuspPuncturedOpen (closureField p)).ι (by rw [AffineCuspSmoothPuncture.smoothLocus_eq_puncture])

private theorem modelPunctureIso_fac :
    (modelPunctureIso p).hom ≫ (cuspPuncturedOpen (closureField p)).ι =
      (AffineCuspSmoothLocus.cuspToBase (closureField p)).smoothLocus.ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The actual geometric relative smooth locus is the puncture used for compact support. -/
def smoothPunctureIso :
    (geometricSmoothOpen p).toScheme ≅ (cuspPuncturedOpen (closureField p)).toScheme :=
  toModelSmooth p ≪≫ modelPunctureIso p

theorem smoothPunctureIso_fac :
    (smoothPunctureIso p).hom ≫ (cuspPuncturedOpen (closureField p)).ι =
      (geometricSmoothOpen p).ι ≫ (affineIso p).hom := by
  change ((toModelSmooth p).hom ≫ (modelPunctureIso p).hom) ≫
    (cuspPuncturedOpen (closureField p)).ι = _
  rw [Category.assoc, modelPunctureIso_fac, toModelSmooth_fac]

/-- The actual geometric fibre sits as an open in the checked proper cusp compactification. -/
def affineCompactOpen : geometricFiber p ⟶ projectiveCusp (closureField p) :=
  (affineIso p).hom ≫ affineOpen (closureField p)

instance affineCompactOpen_isOpenImmersion : IsOpenImmersion (affineCompactOpen p) := by
  letI := CuspProperCompactification.affineOpen_isOpenImmersion (closureField p)
  unfold affineCompactOpen
  infer_instance

/-- Compactification of the genuine relative smooth open by its inclusion in the same ambient curve. -/
def smoothCompactOpen : (geometricSmoothOpen p).toScheme ⟶ projectiveCusp (closureField p) :=
  (geometricSmoothOpen p).ι ≫ affineCompactOpen p

instance smoothCompactOpen_isOpenImmersion : IsOpenImmersion (smoothCompactOpen p) := by
  unfold smoothCompactOpen
  infer_instance

theorem smoothCompactOpen_fac :
    smoothCompactOpen p = (smoothPunctureIso p).hom ≫
      ((cuspPuncturedOpen (closureField p)).ι ≫ affineOpen (closureField p)) := by
  calc
    smoothCompactOpen p =
        ((geometricSmoothOpen p).ι ≫ (affineIso p).hom) ≫ affineOpen (closureField p) :=
      (Category.assoc _ _ _).symm
    _ = ((smoothPunctureIso p).hom ≫ (cuspPuncturedOpen (closureField p)).ι) ≫
        affineOpen (closureField p) := by rw [smoothPunctureIso_fac]
    _ = _ := Category.assoc _ _ _

end
end ManuscriptAudit.IntegralCuspGeometricFiber

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.IntegralCuspGeometricFiber.affineIso,
      ``ManuscriptAudit.IntegralCuspGeometricFiber.affineIso_over,
      ``ManuscriptAudit.IntegralCuspGeometricFiber.smoothPunctureIso,
      ``ManuscriptAudit.IntegralCuspGeometricFiber.smoothPunctureIso_fac,
      ``ManuscriptAudit.IntegralCuspGeometricFiber.affineCompactOpen_isOpenImmersion,
      ``ManuscriptAudit.IntegralCuspGeometricFiber.smoothCompactOpen_isOpenImmersion,
      ``ManuscriptAudit.IntegralCuspGeometricFiber.smoothCompactOpen_fac] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
