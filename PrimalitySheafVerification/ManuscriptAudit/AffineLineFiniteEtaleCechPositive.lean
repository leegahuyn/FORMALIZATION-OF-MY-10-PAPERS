import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineLineNativeRawSections
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineCechRawComparison
import PrimalitySheafVerification.ManuscriptAudit.EtaleProetaleCechAffineUnitComparison
import PrimalitySheafVerification.ManuscriptAudit.EtaleCoefficientLiftCechPositive

/-! On genuine affine étale model arrows, all positive native Čech
degrees of a lifted étale injective are exact. -/

namespace ManuscriptAudit.AffineLineFiniteEtaleCechPositive

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AffineCechConerveSiteComparison (siteMap schemeIso)
open NativeAffineCechRawComparison (nativeArrow nativePresheaf)
open NativeCechNerve (Cech)
open EtaleCoefficientUniverseLift (lift)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K]

private abbrev A := Polynomial K
private abbrev R := CommRingCat.of (A K)
private abbrev X := Spec (R K)

variable (I : Sheaf (X K).smallEtaleTopology AddCommGrpCat.{0}) [Injective I]
  (f : Arrow (Under (R K)))
  [Etale (Spec.map f.left.hom)] [Etale (Spec.map f.right.hom)]

set_option maxHeartbeats 5700000 in
/-- Actual finite affine étale stages provide exact native positive Čech cochains. -/
theorem exactAt_succ (n : ℕ) :
    (Cech (nativeArrow f) (nativePresheaf ((lift (X K)).obj I))).ExactAt (n + 1) := by
  let η := siteMap @Etale f inferInstance inferInstance
  let I' := (lift (X K)).obj I
  have hA (j : ℕ) : IsAffine (CechNerveLowDegrees.N η j).left :=
    IsAffine.of_isIso (schemeIso @Etale f inferInstance inferInstance j).inv
  have hRaw (V : (X K).ProEt) (hV : IsAffine V.left) :
      Function.Bijective ((NativeAffineEtaleKanComparison.toNative (X K) I').app (op V)) := by
    letI := hV
    exact AffineLineNativeRawSections.comparison_bijective K I' V
  have h := EtaleProetaleCechAffineUnitComparison.exactAt_of_exactAt I' η hA hRaw (n + 1)
    (EtaleCoefficientLiftCechPositive.exactAt_succ η I n)
  exact h

end
end ManuscriptAudit.AffineLineFiniteEtaleCechPositive

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineLineFiniteEtaleCechPositive.exactAt_succ
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
