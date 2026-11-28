import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineLineRelativeEtaleCechPositive
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleStageRelativeColimit
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineEtaleStageSmall

/-! Relative affine étale stages compute the actual native Čech
cochains of an arbitrary weakly étale affine chart arrow. -/

namespace ManuscriptAudit.AffineLineNativeCechPositive

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleAffineTensor (structureMap)
open AffineEtaleStageCategory (Stage)
open AffineEtaleStageAlgebraColimit (algebraCocone algebraDiagram isColimit_algebra)
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

variable {B D : Type} [CommRing B] [CommRing D] [Algebra (A K) B] [Algebra (A K) D]
  [Algebra B D] [IsScalarTower (A K) B D]
  [WeaklyEtale (structureMap (A K) B)] [WeaklyEtale (structureMap (A K) D)]
  [WeaklyEtale (structureMap B D)]

private abbrev k := CommRingCat.ofHom (algebraMap (A K) B)
private abbrev arrows := AffineCechRelativeArrowColimit.arrows (k K)
private abbrev diagram := algebraDiagram (A := B) (B := D) ⋙ arrows K
private abbrev cone := (arrows K (B := B)).mapCocone (algebraCocone (A := B) (B := D))
private abbrev algebraArrow := Arrow.mk (IsScalarTower.toAlgHom (A K) B D).toUnder

private def rightIso :
    (cone K (B := B) (D := D)).pt.right ≅ (algebraArrow K (B := B) (D := D)).right :=
  Under.isoMk (Iso.refl _) (by
    change (CommRingCat.ofHom (algebraMap (A K) B) ≫ CommRingCat.ofHom (algebraMap B D)) ≫
      𝟙 (CommRingCat.of D) = CommRingCat.ofHom (algebraMap (A K) D)
    rw [Category.comp_id]
    apply CommRingCat.hom_ext
    ext a
    exact (IsScalarTower.algebraMap_apply (A K) B D a).symm)

private def limitIso : (cone K (B := B) (D := D)).pt ≅ algebraArrow K (B := B) (D := D) :=
  Arrow.isoMk (Iso.refl _) (rightIso K) (by
    apply (Under.forget (R K)).map_injective
    change 𝟙 (CommRingCat.of B) ≫ CommRingCat.ofHom (algebraMap B D) =
      CommRingCat.ofHom (algebraMap B D) ≫ 𝟙 (CommRingCat.of D)
    simp)

private theorem left_limit : WeaklyEtale (Spec.map (cone K (B := B) (D := D)).pt.left.hom) :=
  inferInstanceAs (WeaklyEtale (structureMap (A K) B))

private theorem right_limit : WeaklyEtale (Spec.map (cone K (B := B) (D := D)).pt.right.hom) := by
  have h := Under.w (rightIso K (B := B) (D := D)).hom
  change (cone K (B := B) (D := D)).pt.right.hom ≫ 𝟙 _ =
    CommRingCat.ofHom (algebraMap (A K) D) at h
  rw [Category.comp_id] at h
  rw [h]
  infer_instance

variable (I : Sheaf (X K).smallEtaleTopology AddCommGrpCat.{0}) [Injective I]

set_option maxHeartbeats 10500000 in
/-- The actual affine weakly étale chart arrow has exact positive Čech
cochains for the native image of the universe-lifted étale injective. -/
theorem exactAt_succ (n : ℕ) :
    (Cech (nativeArrow (algebraArrow K (B := B) (D := D)))
      (nativePresheaf ((lift (X K)).obj I))).ExactAt (n + 1) := by
  let J := Stage B D
  letI : EssentiallySmall.{0} J := NativeAffineEtaleStageSmall.essentiallySmall_stage
  letI : HasColimitsOfShape J (Under (R K)) :=
    hasColimitsOfShape_of_equivalence (equivSmallModel.{0} J)
  let I' := (lift (X K)).obj I
  let C := cone K (B := B) (D := D)
  letI : WeaklyEtale (Spec.map C.pt.left.hom) := left_limit K
  letI : WeaklyEtale (Spec.map C.pt.right.hom) := right_limit K
  have hApprox := AffineEtaleStageRelativeColimit.relative_approximation (B := B)
    (AffineLineNativeRawSections.finite_approximation K D inferInstance)
  have hc : IsColimit C := AffineCechRelativeArrowColimit.isColimit_arrows (k K)
    (isColimit_algebra hApprox)
  have hRaw (V : (X K).ProEt) (hV : IsAffine V.left) :
      Function.Bijective ((NativeAffineEtaleKanComparison.toNative (X K) I').app (op V)) := by
    letI := hV
    exact AffineLineNativeRawSections.comparison_bijective K I' V
  have hL (T : J) : WeaklyEtale (Spec.map ((diagram K (B := B) (D := D)).obj T).left.hom) :=
    inferInstanceAs (WeaklyEtale (structureMap (A K) B))
  have hR (T : J) : WeaklyEtale (Spec.map ((diagram K (B := B) (D := D)).obj T).right.hom) :=
    AffineLineRelativeEtaleCechPositive.cover_weaklyEtale K B T.carrier
  have hStage (T : J) :
      (Cech (AffineCechConerveSiteComparison.siteMap @WeaklyEtale
        ((diagram K (B := B) (D := D)).obj T) (hL T) (hR T))
        (nativePresheaf I')).ExactAt (n+1) :=
    AffineLineRelativeEtaleCechPositive.exactAt_succ K B T.carrier I n
  have h := NativeAffineCechArrowContinuity.exactAt_succ I' hRaw C hL hR hc n hStage
  let e := AffineCechSiteArrowDiagram.siteIsoOfRingIso @WeaklyEtale
    inferInstance inferInstance inferInstance inferInstance (limitIso K (B := B) (D := D))
  let j := (NativeCechArrowFunctor.cochains (nativePresheaf I')).mapIso e.symm.op
  exact (HomologicalComplex.exactAt_iff_of_quasiIsoAt j.hom (n+1)).mp h

end
end ManuscriptAudit.AffineLineNativeCechPositive

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineLineNativeCechPositive.exactAt_succ
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
