import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineNativeRawSectionsOfApproximation
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineCechRawComparison
import PrimalitySheafVerification.ManuscriptAudit.EtaleProetaleCechAffineUnitComparison
import PrimalitySheafVerification.ManuscriptAudit.EtaleCoefficientLiftCechPositive

/-! On genuine affine étale model arrows, all positive native Čech
degrees of a lifted étale injective are exact. -/

namespace ManuscriptAudit.AffineFiniteEtaleCechPositiveOfApproximation

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AffineCechConerveSiteComparison (siteMap schemeIso)
open NativeAffineCechRawComparison (nativeArrow nativePresheaf)
open NativeCechNerve (Cech)
open EtaleCoefficientUniverseLift (lift)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (R₀ : Type) [CommRing R₀]

private abbrev A := R₀
private abbrev R := CommRingCat.of (A R₀)
private abbrev X := Spec (R R₀)

variable (hApprox : EtaleBaseChangeFiniteApproximation.HasWeaklyEtaleApproximations R₀)

variable (I : Sheaf (X R₀).smallEtaleTopology AddCommGrpCat.{0}) [Injective I]
  (f : Arrow (Under (R R₀)))
  [Etale (Spec.map f.left.hom)] [Etale (Spec.map f.right.hom)]

include hApprox in
set_option maxHeartbeats 5700000 in
/-- Actual finite affine étale stages provide exact native positive Čech cochains. -/
theorem exactAt_succ (n : ℕ) :
    (Cech (nativeArrow f) (nativePresheaf ((lift (X R₀)).obj I))).ExactAt (n + 1) := by
  let η := siteMap @Etale f inferInstance inferInstance
  let I' := (lift (X R₀)).obj I
  have hA (j : ℕ) : IsAffine (CechNerveLowDegrees.N η j).left :=
    IsAffine.of_isIso (schemeIso @Etale f inferInstance inferInstance j).inv
  have hRaw (V : (X R₀).ProEt) (hV : IsAffine V.left) :
      Function.Bijective ((NativeAffineEtaleKanComparison.toNative (X R₀) I').app (op V)) := by
    letI := hV
    exact AffineNativeRawSectionsOfApproximation.comparison_bijective R₀ hApprox I' V
  have h := EtaleProetaleCechAffineUnitComparison.exactAt_of_exactAt I' η hA hRaw (n + 1)
    (EtaleCoefficientLiftCechPositive.exactAt_succ η I n)
  exact h

end
end ManuscriptAudit.AffineFiniteEtaleCechPositiveOfApproximation

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineFiniteEtaleCechPositiveOfApproximation.exactAt_succ
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
