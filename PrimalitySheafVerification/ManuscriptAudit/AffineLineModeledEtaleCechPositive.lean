import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineLineFiniteEtaleCechPositive
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineCechArrowContinuity
import PrimalitySheafVerification.ManuscriptAudit.AffineCechModelArrowColimit
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleCoverModelIso

/-! Exactness over a relative étale model is obtained along the
actual cofinal tower of finite étale refinements of its base. -/

namespace ManuscriptAudit.AffineLineModeledEtaleCechPositive

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

variable (K : Type) [Field K] [IsAlgClosed K]

private abbrev A := Polynomial K
private abbrev X := Spec (CommRingCat.of (A K))

variable {B : Type} [CommRing B] [Algebra (A K) B] [WeaklyEtale (structureMap (A K) B)]
  (T : Stage (A K) B) (E : Type) [CommRing E] [Algebra T.carrier E] [Algebra.Etale T.carrier E]

abbrev arrowFunctor := AffineCechModelArrowColimit.arrows (baseArrow T) (fixedRing T E)
abbrev arrowCocone := (arrowFunctor K T E).mapCocone (refinementCocone T)

private abbrev F := refinementDiagram T ⋙ arrowFunctor K T E
private abbrev C := refinementCocone T

private theorem etale_model :
    Etale (Spec.map (fixedRing T E).hom) :=
  (HasRingHomProperty.Spec_iff (P := @Etale) (φ := (fixedRing T E).hom)).mpr
    ((RingHom.etale_algebraMap).mpr inferInstance)

private theorem etale_base (j : Under T) : Etale (Spec.map ((F K T E).obj j).left.hom) := by
  have h : ((F K T E).obj j).left.hom = CommRingCat.ofHom (algebraMap (A K) j.right.carrier) := by
    apply CommRingCat.hom_ext
    ext a
    exact (hom j.hom).commutes a
  rw [h]
  exact (HasRingHomProperty.Spec_iff (P := @Etale) (φ := CommRingCat.ofHom
    (algebraMap (A K) j.right.carrier))).mpr ((RingHom.etale_algebraMap).mpr inferInstance)

private theorem etale_cover (j : Under T) : Etale (Spec.map ((F K T E).obj j).right.hom) := by
  let f := (F K T E).obj j
  letI : Etale (Spec.map f.left.hom) := etale_base K T E j
  letI : Etale (Spec.map f.hom.right) :=
    AffineStageFixedCoproductGeometry.etale_cover ((refinementDiagram T).obj j)
      (fixedRing T E) (etale_model K T E)
  change Etale (Spec.map f.right.hom)
  rw [← Under.w f.hom, Spec.map_comp]
  infer_instance

instance limit_base_weaklyEtale :
    WeaklyEtale (Spec.map (arrowCocone K T E).pt.left.hom) := by
  have h := Under.w (baseIso T).hom
  change (arrowCocone K T E).pt.left.hom ≫ 𝟙 _ = CommRingCat.ofHom (algebraMap (A K) B) at h
  rw [Category.comp_id] at h
  rw [h]
  infer_instance

instance limit_cover_weaklyEtale :
    WeaklyEtale (Spec.map (arrowCocone K T E).pt.right.hom) := by
  let f := (arrowCocone K T E).pt
  letI : WeaklyEtale (Spec.map f.left.hom) := limit_base_weaklyEtale K T E
  letI : Etale (Spec.map f.hom.right) :=
    AffineStageFixedCoproductGeometry.etale_cover (C T).pt (fixedRing T E) (etale_model K T E)
  change WeaklyEtale (Spec.map f.right.hom)
  rw [← Under.w f.hom, Spec.map_comp]
  infer_instance

variable (I : Sheaf (X K).smallEtaleTopology AddCommGrpCat.{0}) [Injective I]

set_option maxHeartbeats 7800000 in
/-- Every positive degree is exact on a relative model after the
actual continuous affine base change. -/
theorem exactAt_succ (n : ℕ) :
    (Cech (nativeArrow (arrowCocone K T E).pt)
      (nativePresheaf ((lift (X K)).obj I))).ExactAt (n + 1) := by
  let J := Under T
  letI : HasColimitsOfShape J (Under (CommRingCat.of (A K))) :=
    hasColimitsOfShape_of_equivalence (equivSmallModel.{0} J)
  let I' := (lift (X K)).obj I
  have hRaw (V : (X K).ProEt) (hV : IsAffine V.left) :
      Function.Bijective ((NativeAffineEtaleKanComparison.toNative (X K) I').app (op V)) := by
    letI := hV
    exact AffineLineNativeRawSections.comparison_bijective K I' V
  have hC := AffineCechModelArrowColimit.isColimit_arrows (baseArrow T) (fixedRing T E)
    (isColimit_refinement T (AffineLineNativeRawSections.finite_approximation K B inferInstance))
  apply NativeAffineCechArrowContinuity.exactAt_succ I' hRaw (arrowCocone K T E)
    (fun j ↦ (etale_base K T E j).weaklyEtale) (fun j ↦ (etale_cover K T E j).weaklyEtale) hC n
  intro j
  letI := etale_base K T E j
  letI := etale_cover K T E j
  exact AffineLineFiniteEtaleCechPositive.exactAt_succ K I ((F K T E).obj j) n

end
end ManuscriptAudit.AffineLineModeledEtaleCechPositive

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineLineModeledEtaleCechPositive.exactAt_succ
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
