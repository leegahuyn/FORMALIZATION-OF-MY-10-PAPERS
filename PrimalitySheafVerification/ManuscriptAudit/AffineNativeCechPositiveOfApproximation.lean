import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineRelativeEtaleCechPositiveOfApproximation
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleStageRelativeColimit
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineEtaleStageSmall

/-! Relative affine étale stages compute the actual native Čech
cochains of an arbitrary weakly étale affine chart arrow. -/

namespace ManuscriptAudit.AffineNativeCechPositiveOfApproximation

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

variable (R₀ : Type) [CommRing R₀]

private abbrev A := R₀
private abbrev R := CommRingCat.of (A R₀)
private abbrev X := Spec (R R₀)

variable (hApprox : EtaleBaseChangeFiniteApproximation.HasWeaklyEtaleApproximations R₀)

variable {B D : Type} [CommRing B] [CommRing D] [Algebra (A R₀) B] [Algebra (A R₀) D]
  [Algebra B D] [IsScalarTower (A R₀) B D]
  [WeaklyEtale (structureMap (A R₀) B)] [WeaklyEtale (structureMap (A R₀) D)]
  [WeaklyEtale (structureMap B D)]

private abbrev k := CommRingCat.ofHom (algebraMap (A R₀) B)
private abbrev arrows := AffineCechRelativeArrowColimit.arrows (k R₀)
private abbrev diagram := algebraDiagram (A := B) (B := D) ⋙ arrows R₀
private abbrev cone := (arrows R₀ (B := B)).mapCocone (algebraCocone (A := B) (B := D))
private abbrev algebraArrow := Arrow.mk (IsScalarTower.toAlgHom (A R₀) B D).toUnder

private def rightIso :
    (cone R₀ (B := B) (D := D)).pt.right ≅ (algebraArrow R₀ (B := B) (D := D)).right :=
  Under.isoMk (Iso.refl _) (by
    change (CommRingCat.ofHom (algebraMap (A R₀) B) ≫ CommRingCat.ofHom (algebraMap B D)) ≫
      𝟙 (CommRingCat.of D) = CommRingCat.ofHom (algebraMap (A R₀) D)
    rw [Category.comp_id]
    apply CommRingCat.hom_ext
    ext a
    exact (IsScalarTower.algebraMap_apply (A R₀) B D a).symm)

private def limitIso : (cone R₀ (B := B) (D := D)).pt ≅ algebraArrow R₀ (B := B) (D := D) :=
  Arrow.isoMk (Iso.refl _) (rightIso R₀) (by
    apply (Under.forget (R R₀)).map_injective
    change 𝟙 (CommRingCat.of B) ≫ CommRingCat.ofHom (algebraMap B D) =
      CommRingCat.ofHom (algebraMap B D) ≫ 𝟙 (CommRingCat.of D)
    simp)

private theorem left_limit : WeaklyEtale (Spec.map (cone R₀ (B := B) (D := D)).pt.left.hom) :=
  inferInstanceAs (WeaklyEtale (structureMap (A R₀) B))

private theorem right_limit : WeaklyEtale (Spec.map (cone R₀ (B := B) (D := D)).pt.right.hom) := by
  have h := Under.w (rightIso R₀ (B := B) (D := D)).hom
  change (cone R₀ (B := B) (D := D)).pt.right.hom ≫ 𝟙 _ =
    CommRingCat.ofHom (algebraMap (A R₀) D) at h
  rw [Category.comp_id] at h
  rw [h]
  infer_instance

variable (I : Sheaf (X R₀).smallEtaleTopology AddCommGrpCat.{0}) [Injective I]

include hApprox in
set_option maxHeartbeats 10500000 in
/-- The actual affine weakly étale chart arrow has exact positive Čech
cochains for the native image of the universe-lifted étale injective. -/
theorem exactAt_succ (n : ℕ) :
    (Cech (nativeArrow (algebraArrow R₀ (B := B) (D := D)))
      (nativePresheaf ((lift (X R₀)).obj I))).ExactAt (n + 1) := by
  let J := Stage B D
  letI : EssentiallySmall.{0} J := NativeAffineEtaleStageSmall.essentiallySmall_stage
  letI : HasColimitsOfShape J (Under (R R₀)) :=
    hasColimitsOfShape_of_equivalence (equivSmallModel.{0} J)
  let I' := (lift (X R₀)).obj I
  let C := cone R₀ (B := B) (D := D)
  letI : WeaklyEtale (Spec.map C.pt.left.hom) := left_limit R₀
  letI : WeaklyEtale (Spec.map C.pt.right.hom) := right_limit R₀
  have hRelativeApprox := AffineEtaleStageRelativeColimit.relative_approximation (B := B)
    (AffineNativeRawSectionsOfApproximation.finite_approximation R₀ hApprox D inferInstance)
  have hc : IsColimit C := AffineCechRelativeArrowColimit.isColimit_arrows (k R₀)
    (isColimit_algebra hRelativeApprox)
  have hRaw (V : (X R₀).ProEt) (hV : IsAffine V.left) :
      Function.Bijective ((NativeAffineEtaleKanComparison.toNative (X R₀) I').app (op V)) := by
    letI := hV
    exact AffineNativeRawSectionsOfApproximation.comparison_bijective R₀ hApprox I' V
  have hL (T : J) : WeaklyEtale (Spec.map ((diagram R₀ (B := B) (D := D)).obj T).left.hom) :=
    inferInstanceAs (WeaklyEtale (structureMap (A R₀) B))
  have hR (T : J) : WeaklyEtale (Spec.map ((diagram R₀ (B := B) (D := D)).obj T).right.hom) :=
    AffineRelativeEtaleCechPositiveOfApproximation.cover_weaklyEtale R₀ B T.carrier
  have hStage (T : J) :
      (Cech (AffineCechConerveSiteComparison.siteMap @WeaklyEtale
        ((diagram R₀ (B := B) (D := D)).obj T) (hL T) (hR T))
        (nativePresheaf I')).ExactAt (n+1) :=
    AffineRelativeEtaleCechPositiveOfApproximation.exactAt_succ R₀ hApprox B T.carrier I n
  have h := NativeAffineCechArrowContinuity.exactAt_succ I' hRaw C hL hR hc n hStage
  let e := AffineCechSiteArrowDiagram.siteIsoOfRingIso @WeaklyEtale
    inferInstance inferInstance inferInstance inferInstance (limitIso R₀ (B := B) (D := D))
  let j := (NativeCechArrowFunctor.cochains (nativePresheaf I')).mapIso e.symm.op
  exact (HomologicalComplex.exactAt_iff_of_quasiIsoAt j.hom (n+1)).mp h

end
end ManuscriptAudit.AffineNativeCechPositiveOfApproximation

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineNativeCechPositiveOfApproximation.exactAt_succ
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
