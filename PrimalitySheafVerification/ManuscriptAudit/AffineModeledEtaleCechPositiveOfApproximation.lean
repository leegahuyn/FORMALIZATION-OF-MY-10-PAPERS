import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineFiniteEtaleCechPositiveOfApproximation
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineCechArrowContinuity
import PrimalitySheafVerification.ManuscriptAudit.AffineCechModelArrowColimit
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleCoverModelIso

/-! Exactness over a relative étale model is obtained along the
actual cofinal tower of finite étale refinements of its base. -/

namespace ManuscriptAudit.AffineModeledEtaleCechPositiveOfApproximation

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleAffineTensor (structureMap)
open AffineEtaleStageCategory (Stage hom)
open AffineEtaleCoverModelIso (baseArrow baseIso fixedRing)
open AffineEtaleStageRefinementColimit (refinementCocone refinementDiagram isColimit_refinement)
open NativeAffineCechRawComparison (nativeArrow nativePresheaf)
open NativeCechNerve (Cech)
open EtaleCoefficientUniverseLift (lift)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (R₀ : Type) [CommRing R₀]

private abbrev A := R₀
private abbrev X := Spec (CommRingCat.of (A R₀))

variable (hApprox : EtaleBaseChangeFiniteApproximation.HasWeaklyEtaleApproximations R₀)

variable {B : Type} [CommRing B] [Algebra (A R₀) B] [WeaklyEtale (structureMap (A R₀) B)]
  (T : Stage (A R₀) B) (E : Type) [CommRing E] [Algebra T.carrier E] [Algebra.Etale T.carrier E]

abbrev arrowFunctor := AffineCechModelArrowColimit.arrows (baseArrow T) (fixedRing T E)
abbrev arrowCocone := (arrowFunctor R₀ T E).mapCocone (refinementCocone T)

private abbrev F := refinementDiagram T ⋙ arrowFunctor R₀ T E
private abbrev C := refinementCocone T

private theorem etale_model :
    Etale (Spec.map (fixedRing T E).hom) :=
  (HasRingHomProperty.Spec_iff (P := @Etale) (φ := (fixedRing T E).hom)).mpr
    ((RingHom.etale_algebraMap).mpr inferInstance)

private theorem etale_base (j : Under T) : Etale (Spec.map ((F R₀ T E).obj j).left.hom) := by
  have h : ((F R₀ T E).obj j).left.hom = CommRingCat.ofHom (algebraMap (A R₀) j.right.carrier) := by
    apply CommRingCat.hom_ext
    ext a
    exact (hom j.hom).commutes a
  rw [h]
  exact (HasRingHomProperty.Spec_iff (P := @Etale) (φ := CommRingCat.ofHom
    (algebraMap (A R₀) j.right.carrier))).mpr ((RingHom.etale_algebraMap).mpr inferInstance)

private theorem etale_cover (j : Under T) : Etale (Spec.map ((F R₀ T E).obj j).right.hom) := by
  let f := (F R₀ T E).obj j
  letI : Etale (Spec.map f.left.hom) := etale_base R₀ T E j
  letI : Etale (Spec.map f.hom.right) :=
    AffineStageFixedCoproductGeometry.etale_cover ((refinementDiagram T).obj j)
      (fixedRing T E) (etale_model R₀ T E)
  change Etale (Spec.map f.right.hom)
  rw [← Under.w f.hom, Spec.map_comp]
  infer_instance

instance limit_base_weaklyEtale :
    WeaklyEtale (Spec.map (arrowCocone R₀ T E).pt.left.hom) := by
  have h := Under.w (baseIso T).hom
  change (arrowCocone R₀ T E).pt.left.hom ≫ 𝟙 _ = CommRingCat.ofHom (algebraMap (A R₀) B) at h
  rw [Category.comp_id] at h
  rw [h]
  infer_instance

instance limit_cover_weaklyEtale :
    WeaklyEtale (Spec.map (arrowCocone R₀ T E).pt.right.hom) := by
  let f := (arrowCocone R₀ T E).pt
  letI : WeaklyEtale (Spec.map f.left.hom) := limit_base_weaklyEtale R₀ T E
  letI : Etale (Spec.map f.hom.right) :=
    AffineStageFixedCoproductGeometry.etale_cover (C T).pt (fixedRing T E) (etale_model R₀ T E)
  change WeaklyEtale (Spec.map f.right.hom)
  rw [← Under.w f.hom, Spec.map_comp]
  infer_instance

variable (I : Sheaf (X R₀).smallEtaleTopology AddCommGrpCat.{0}) [Injective I]

include hApprox in
set_option maxHeartbeats 7800000 in
/-- Every positive degree is exact on a relative model after the
actual continuous affine base change. -/
theorem exactAt_succ (n : ℕ) :
    (Cech (nativeArrow (arrowCocone R₀ T E).pt)
      (nativePresheaf ((lift (X R₀)).obj I))).ExactAt (n + 1) := by
  let J := Under T
  letI : HasColimitsOfShape J (Under (CommRingCat.of (A R₀))) :=
    hasColimitsOfShape_of_equivalence (equivSmallModel.{0} J)
  let I' := (lift (X R₀)).obj I
  have hRaw (V : (X R₀).ProEt) (hV : IsAffine V.left) :
      Function.Bijective ((NativeAffineEtaleKanComparison.toNative (X R₀) I').app (op V)) := by
    letI := hV
    exact AffineNativeRawSectionsOfApproximation.comparison_bijective R₀ hApprox I' V
  have hC := AffineCechModelArrowColimit.isColimit_arrows (baseArrow T) (fixedRing T E)
    (isColimit_refinement T (AffineNativeRawSectionsOfApproximation.finite_approximation R₀ hApprox B inferInstance))
  apply NativeAffineCechArrowContinuity.exactAt_succ I' hRaw (arrowCocone R₀ T E)
    (fun j ↦ (etale_base R₀ T E j).weaklyEtale) (fun j ↦ (etale_cover R₀ T E j).weaklyEtale) hC n
  intro j
  letI := etale_base R₀ T E j
  letI := etale_cover R₀ T E j
  exact AffineFiniteEtaleCechPositiveOfApproximation.exactAt_succ R₀ hApprox I ((F R₀ T E).obj j) n

end
end ManuscriptAudit.AffineModeledEtaleCechPositiveOfApproximation

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineModeledEtaleCechPositiveOfApproximation.exactAt_succ
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
