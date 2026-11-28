import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.WeaklyEtaleAffineLineGlobalStage
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineRawSingletonGluingTransport
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineRawComparisonDescent

/-! On the affine line over an algebraically closed field, the
native inverse image is computed by the actual affine étale stage colimit. -/

namespace ManuscriptAudit.AffineLineNativeRawSections

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AffineEtaleStageColimit (FiniteTupleApproximation)
open ProetaleAffineTensor (spectrum structureMap)
open NativeAffineEtaleKanComparison (raw toNative)
open NativeAffineEtaleStageSections (sectionCocone)
open NativeAffineEtaleRawSections (isColimit_rawSectionCocone raw_toNative_fac)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K]

private abbrev A := Polynomial K
private abbrev X := spectrum (A K)
private abbrev G := AddCommGrpCat.{1}

theorem finite_approximation (B : Type) [CommRing B] [Algebra (A K) B]
    (h : WeaklyEtale (structureMap (A K) B)) : FiniteTupleApproximation (A K) B := by
  letI := h
  intro ι _ w
  exact WeaklyEtaleAffineLineGlobalStage.exists_global_stage K B w

variable (I : Sheaf (X K).smallEtaleTopology G)

set_option maxHeartbeats 3800000 in
/-- The affine raw-to-native comparison on the actual pro-étale site
is bijective for any affine chart, with no descent premise. -/
theorem comparison_bijective (V : (X K).ProEt) [IsAffine V.left] :
    Function.Bijective ((toNative (X K) I).app (op V)) :=
  NativeAffineRawComparisonDescent.comparison_bijective I (finite_approximation K)
    (NativeAffineRawSingletonGluingTransport.affineSingletonGluing I (finite_approximation K)) V

/-- The actual adjunction unit is surjective on the actual terminal
small étale object of the affine line. -/
theorem unit_terminal_surjective :
    Function.Surjective (((EtaleProetaleInverseImage.adjunction (X K)).unit.app I).hom.app
      (op (Scheme.Etale.mk (𝟙 (X K))))) :=
  NativeAffineRawComparisonDescent.unit_terminal_surjective I (finite_approximation K)
    (NativeAffineRawSingletonGluingTransport.affineSingletonGluing I (finite_approximation K))

set_option maxHeartbeats 3800000 in
/-- The actual inverse-image evaluations are genuine filtered
colimits of the actual étale evaluations, with the original restriction maps. -/
def isColimit_native (B : Type) [CommRing B] [Algebra (A K) B]
    [WeaklyEtale (structureMap (A K) B)] : IsColimit (sectionCocone (B := B) I) := by
  let V := ProetaleAffineTensor.object (A K) B
  let f := (toNative (X K) I).app (op V)
  let j := (AddEquiv.ofBijective f.hom (comparison_bijective K I V)).toAddCommGrpIso
  exact IsColimit.ofIsoColimit (isColimit_rawSectionCocone (B := B) I)
    (Cocone.ext j (fun T ↦ raw_toNative_fac (B := B) I T))

end
end ManuscriptAudit.AffineLineNativeRawSections

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineLineNativeRawSections.comparison_bijective,
      ``ManuscriptAudit.AffineLineNativeRawSections.unit_terminal_surjective,
      ``ManuscriptAudit.AffineLineNativeRawSections.isColimit_native] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
