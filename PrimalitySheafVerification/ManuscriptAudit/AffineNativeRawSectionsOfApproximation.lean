import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleBaseChangeFiniteApproximation
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineRawSingletonGluingTransport
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineRawComparisonDescent

/-! For affine bases with weakly étale finite approximations, the
native inverse image is computed by the actual affine étale stage colimit. -/

namespace ManuscriptAudit.AffineNativeRawSectionsOfApproximation

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AffineEtaleStageColimit (FiniteTupleApproximation)
open ProetaleAffineTensor (spectrum structureMap)
open NativeAffineEtaleKanComparison (raw toNative)
open NativeAffineEtaleStageSections (sectionCocone)
open NativeAffineEtaleRawSections (isColimit_rawSectionCocone raw_toNative_fac)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (R₀ : Type) [CommRing R₀]

private abbrev A := R₀
private abbrev X := spectrum (A R₀)

variable (hApprox : EtaleBaseChangeFiniteApproximation.HasWeaklyEtaleApproximations R₀)
private abbrev G := AddCommGrpCat.{1}

include hApprox in
theorem finite_approximation (B : Type) [CommRing B] [Algebra (A R₀) B]
    (h : WeaklyEtale (structureMap (A R₀) B)) : FiniteTupleApproximation (A R₀) B := by
  letI := h
  intro ι _ w
  exact hApprox B w

variable (I : Sheaf (X R₀).smallEtaleTopology G)

include hApprox in
set_option maxHeartbeats 3800000 in
/-- The affine raw-to-native comparison on the actual pro-étale site
is bijective on each affine chart of the base. -/
theorem comparison_bijective (V : (X R₀).ProEt) [IsAffine V.left] :
    Function.Bijective ((toNative (X R₀) I).app (op V)) :=
  NativeAffineRawComparisonDescent.comparison_bijective I (finite_approximation R₀ hApprox)
    (NativeAffineRawSingletonGluingTransport.affineSingletonGluing I (finite_approximation R₀ hApprox)) V

include hApprox in
/-- The actual adjunction unit is surjective on the actual terminal
small étale object of the affine base. -/
theorem unit_terminal_surjective :
    Function.Surjective (((EtaleProetaleInverseImage.adjunction (X R₀)).unit.app I).hom.app
      (op (Scheme.Etale.mk (𝟙 (X R₀))))) :=
  NativeAffineRawComparisonDescent.unit_terminal_surjective I (finite_approximation R₀ hApprox)
    (NativeAffineRawSingletonGluingTransport.affineSingletonGluing I (finite_approximation R₀ hApprox))

include hApprox in
set_option maxHeartbeats 3800000 in
/-- The actual inverse-image evaluations are genuine filtered
colimits of the actual étale evaluations, with the original restriction maps. -/
def isColimit_native (B : Type) [CommRing B] [Algebra (A R₀) B]
    [WeaklyEtale (structureMap (A R₀) B)] : IsColimit (sectionCocone (B := B) I) := by
  let V := ProetaleAffineTensor.object (A R₀) B
  let f := (toNative (X R₀) I).app (op V)
  let j := (AddEquiv.ofBijective f.hom (comparison_bijective R₀ hApprox I V)).toAddCommGrpIso
  exact IsColimit.ofIsoColimit (isColimit_rawSectionCocone (B := B) I)
    (Cocone.ext j (fun T ↦ raw_toNative_fac (B := B) I T))

end
end ManuscriptAudit.AffineNativeRawSectionsOfApproximation

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineNativeRawSectionsOfApproximation.comparison_bijective,
      ``ManuscriptAudit.AffineNativeRawSectionsOfApproximation.unit_terminal_surjective,
      ``ManuscriptAudit.AffineNativeRawSectionsOfApproximation.isColimit_native] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
