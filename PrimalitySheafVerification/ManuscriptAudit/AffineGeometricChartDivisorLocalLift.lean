import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineGeometricChartDivisorMap
import PrimalitySheafVerification.ManuscriptAudit.DedekindDivisorLocalLift

/-!
# Actual local lifts of divisor-sheaf sections

A finite divisor section on an integral affine étale chart lifts to
generic units after restriction to a principal open neighborhood of
any specified point. The neighborhood uses the actual localization
and the restriction in the affine étale site.
-/

namespace ManuscriptAudit.AffineGeometricChartDivisorLocalLift

open AlgebraicGeometry CategoryTheory Opposite
open AffineEtaleGenericField GenericEtaleUnitSections
open DedekindPrincipalDivisor DedekindEtaleGenericDivisor
open AffineGeometricDivisorSheaf AffineGeometricDivisorSections AffineGeometricDivisorNaturality
open AffineGeometricChartDivisorMap

open scoped TensorProduct

noncomputable section

attribute [local instance] Algebra.TensorProduct.rightAlgebra

set_option backward.isDefEq.respectTransparency false

variable (K A B F : Type) [Field K] [IsAlgClosed K] [CommRing A] [IsDedekindDomain A]
  [Algebra K A] [Algebra.FiniteType K A] [CommRing B] [IsDomain B] [Field F]
  [Algebra A B] [Algebra.Etale A B] [Algebra A F] [IsFractionRing A F]

set_option maxHeartbeats 1400000 in
/-- Every actual divisor section lifts locally to a generic unit around
each prime of the given integral affine étale chart. -/
theorem chartDivisorMap_localLift (x : PrimeSpectrum B)
    (d : (affineDivisorSheaf K A).obj.obj (op (chartObject A B))) :
    ∃ (b : B) (hb : b ∉ x.asIdeal) (u : genericUnitSectionGroup A B F),
      let C := Localization.Away b
      letI : IsDomain C := Localization.Away.isDomain (fun h ↦ hb (h.symm ▸ x.asIdeal.zero_mem))
      letI : Algebra.Etale B C := Algebra.Etale.of_isLocalizationAway b
      (affineDivisorSheaf K A).obj.map (chartArrow A B C).op (chartDivisorMap K A B F u) =
        (affineDivisorSheaf K A).obj.map (chartArrow A B C).op d := by
  let L := F ⊗[A] B
  letI : Field L := (genericFiber_isField A B F).toField
  letI : IsFractionRing B L := genericFiber_isFractionRing A B F
  letI : IsDedekindDomain B := AffineEtaleOverDedekind.isDedekindDomain A B
  let e := (genericUnitSectionsIso A B F).addCommGroupIsoToAddEquiv
  let eD := chartSectionsEquiv K A B
  obtain ⟨b, hb, v, hv⟩ := exists_principalOpen_divisorLift B L x (eD d)
  refine ⟨b, hb, e.symm v, ?_⟩
  let C := Localization.Away b
  letI : IsDomain C := Localization.Away.isDomain (fun h ↦ hb (h.symm ▸ x.asIdeal.zero_mem))
  letI : Algebra.Etale B C := Algebra.Etale.of_isLocalizationAway b
  change (affineDivisorSheaf K A).obj.map (chartArrow A B C).op (chartDivisorMap K A B F (e.symm v)) =
    (affineDivisorSheaf K A).obj.map (chartArrow A B C).op d
  apply (chartSectionsEquiv K A C).injective
  rw [chartSectionsEquiv_restrict, chartSectionsEquiv_restrict]
  change AffineEtaleClosedPoints.pullback B C (eD (eD.symm (principalDivisor B L (e (e.symm v))))) =
    AffineEtaleClosedPoints.pullback B C (eD d)
  rw [eD.apply_symm_apply, e.apply_symm_apply]
  apply Finsupp.ext
  intro q
  simp only [AffineEtaleClosedPoints.pullback_apply]
  apply hv
  intro h
  have hu : IsUnit (algebraMap B C b) := IsLocalization.Away.algebraMap_isUnit b
  exact q.isPrime.ne_top (q.asIdeal.eq_top_of_isUnit_mem h hu)

end

end ManuscriptAudit.AffineGeometricChartDivisorLocalLift

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.AffineGeometricChartDivisorLocalLift.chartDivisorMap_localLift
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
