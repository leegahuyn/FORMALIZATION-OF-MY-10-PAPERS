import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalSmoothLocus
import PrimalitySheafVerification.ManuscriptAudit.NodalChartIntersection

/-! The actual smooth nodal locus is covered by its punctured affine Z-chart
and its Y-chart. Their scheme intersection is the checked normalized
parameter localization. -/

namespace ManuscriptAudit.NodalSmoothLocusOverlap

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NodalProjectiveClosure (affineNode affineOpen projectiveNode projectiveNodeToBase)
open NodalProperYChart (chartOpen)
open NodalSmoothLocus (conductorOpen smoothLocus_eq_complement smooth_pieces_cover_complement)
open NodalChartIntersection (intersectionIsoParameter intersectionIsoParameter_inv_fst
  intersectionIsoParameter_inv_snd)
open NodalConductor (coordinates)
open NodalAffinePresentation (nodeX)
open NodalYChartImmersion (nodeYChart)
open NodalYChartOverlap (parameterRing)
open NodalYChartOverlapPlane (parameterScheme zParameter toAffineNode toNodeYChart)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (K : Type u) [Field K]

abbrev puncturedZRing := Localization.Away (nodeX K)
abbrev puncturedZ : Scheme.{u} := Spec (CommRingCat.of (puncturedZRing K))

def puncturedZ_toAffine : puncturedZ K ⟶ affineNode K :=
  Spec.map (CommRingCat.ofHom (algebraMap (coordinates K) (puncturedZRing K)))

instance puncturedZ_toAffine_open : IsOpenImmersion (puncturedZ_toAffine K) :=
  IsOpenImmersion.of_isLocalization (S := puncturedZRing K) (nodeX K)

theorem conductorOpen_factors :
    conductorOpen K = puncturedZ_toAffine K ≫ affineOpen K := rfl

abbrev smoothOpen : (projectiveNode K).Opens := (projectiveNodeToBase K).smoothLocus
abbrev smoothScheme : Scheme.{u} := (smoothOpen K).toScheme

private theorem twoRanges_eq_smoothRange :
    Set.range (conductorOpen K) ∪ Set.range (chartOpen K) = Set.range (smoothOpen K).ι := by
  rw [smooth_pieces_cover_complement, Scheme.Opens.range_ι, smoothLocus_eq_complement]

private theorem z_range :
    Set.range (conductorOpen K) ⊆ Set.range (smoothOpen K).ι := by
  rw [← twoRanges_eq_smoothRange]
  exact Set.subset_union_left

private theorem y_range :
    Set.range (chartOpen K) ⊆ Set.range (smoothOpen K).ι := by
  rw [← twoRanges_eq_smoothRange]
  exact Set.subset_union_right

def zSmooth : puncturedZ K ⟶ smoothScheme K :=
  IsOpenImmersion.lift (smoothOpen K).ι (conductorOpen K) (z_range K)

def ySmooth : nodeYChart K ⟶ smoothScheme K :=
  IsOpenImmersion.lift (smoothOpen K).ι (chartOpen K) (y_range K)

instance zSmooth_open : IsOpenImmersion (zSmooth K) := by
  unfold zSmooth
  infer_instance

instance ySmooth_open : IsOpenImmersion (ySmooth K) := by
  unfold ySmooth
  infer_instance

@[reassoc]
theorem zSmooth_ambient : zSmooth K ≫ (smoothOpen K).ι = conductorOpen K :=
  IsOpenImmersion.lift_fac _ _ _

@[reassoc]
theorem ySmooth_ambient : ySmooth K ≫ (smoothOpen K).ι = chartOpen K :=
  IsOpenImmersion.lift_fac _ _ _

theorem smooth_charts_cover : Set.range (zSmooth K) ∪ Set.range (ySmooth K) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  have hp : (smoothOpen K).ι p ∈ Set.range (smoothOpen K).ι := ⟨p, rfl⟩
  rw [← twoRanges_eq_smoothRange] at hp
  rcases hp with ⟨q, hq⟩ | ⟨q, hq⟩
  · left
    refine ⟨q, (smoothOpen K).ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, zSmooth_ambient]
    exact hq
  · right
    refine ⟨q, (smoothOpen K).ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, ySmooth_ambient]
    exact hq

private theorem old_parameter_square :
    toAffineNode K ≫ affineOpen K = toNodeYChart K ≫ chartOpen K := by
  rw [← intersectionIsoParameter_inv_fst, ← intersectionIsoParameter_inv_snd,
    Category.assoc, Category.assoc, pullback.condition]

private theorem old_parameter_pullback :
    IsPullback (toAffineNode K) (toNodeYChart K) (affineOpen K) (chartOpen K) :=
  IsPullback.of_iso_pullback ⟨old_parameter_square K⟩ (intersectionIsoParameter K).symm
    (intersectionIsoParameter_inv_fst K) (intersectionIsoParameter_inv_snd K)

private theorem nodeX_parameter_isUnit : IsUnit (zParameter K (nodeX K)) := by
  let f := algebraMap (Polynomial K) (parameterRing K)
  change IsUnit (f (NodalConductor.x K))
  have h : IsUnit (f (NodalConductor.x K * Polynomial.X)) :=
    IsLocalization.Away.algebraMap_isUnit (S := parameterRing K) (NodalConductor.y K)
  exact (IsUnit.mul_iff.mp ((f.map_mul _ _) ▸ h)).1

def zParameterLocal : puncturedZRing K →ₐ[K] parameterRing K :=
  IsLocalization.Away.liftAlgHom (nodeX K) (f := zParameter K) (nodeX_parameter_isUnit K)

theorem zParameterLocal_on_affine (a : coordinates K) :
    zParameterLocal K (algebraMap (coordinates K) (puncturedZRing K) a) = zParameter K a := by
  unfold zParameterLocal
  rw [IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq] <;> rfl

def toPuncturedZ : parameterScheme K ⟶ puncturedZ K :=
  Spec.map (CommRingCat.ofHom (zParameterLocal K).toRingHom)

@[reassoc]
theorem toPuncturedZ_toAffine :
    toPuncturedZ K ≫ puncturedZ_toAffine K = toAffineNode K := by
  unfold toPuncturedZ puncturedZ_toAffine toAffineNode
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact zParameterLocal_on_affine K a

instance toPuncturedZ_open : IsOpenImmersion (toPuncturedZ K) := by
  haveI : IsOpenImmersion (toAffineNode K) := by
    rw [← intersectionIsoParameter_inv_fst]
    infer_instance
  haveI : IsOpenImmersion (toPuncturedZ K ≫ puncturedZ_toAffine K) := by
    rw [toPuncturedZ_toAffine]
    infer_instance
  exact IsOpenImmersion.of_comp _ (puncturedZ_toAffine K)

private theorem smooth_square :
    toPuncturedZ K ≫ zSmooth K = toNodeYChart K ≫ ySmooth K := by
  apply (cancel_mono ((smoothOpen K).ι)).mp
  rw [Category.assoc, zSmooth_ambient, Category.assoc, ySmooth_ambient,
    conductorOpen_factors, toPuncturedZ_toAffine_assoc, old_parameter_square]

/-- The actual scheme intersection on the smooth locus is the normalized parameter scheme. -/
theorem smooth_parameter_pullback :
    IsPullback (toPuncturedZ K) (toNodeYChart K) (zSmooth K) (ySmooth K) := by
  let h := old_parameter_pullback K
  have liftCondition (s : PullbackCone (zSmooth K) (ySmooth K)) :
      (s.fst ≫ puncturedZ_toAffine K) ≫ affineOpen K = s.snd ≫ chartOpen K := by
    rw [Category.assoc, ← conductorOpen_factors, ← zSmooth_ambient, ← ySmooth_ambient,
      ← Category.assoc, ← Category.assoc, s.condition]
  let l (s : PullbackCone (zSmooth K) (ySmooth K)) :
      s.pt ⟶ parameterScheme K :=
    h.lift (s.fst ≫ puncturedZ_toAffine K) s.snd (liftCondition s)
  apply IsPullback.of_isLimit (PullbackCone.IsLimit.mk (smooth_square K) l ?_ ?_ ?_)
  · intro s
    apply (cancel_mono (puncturedZ_toAffine K)).mp
    rw [Category.assoc, toPuncturedZ_toAffine]
    exact h.lift_fst _ _ _
  · intro s
    exact h.lift_snd _ _ _
  · intro s m hm₁ hm₂
    apply h.hom_ext
    · calc
        m ≫ toAffineNode K = (m ≫ toPuncturedZ K) ≫ puncturedZ_toAffine K := by
          rw [Category.assoc, toPuncturedZ_toAffine]
        _ = s.fst ≫ puncturedZ_toAffine K := congrArg (fun a => a ≫ puncturedZ_toAffine K) hm₁
        _ = _ := (h.lift_fst _ _ _).symm
    · exact hm₂.trans (h.lift_snd _ _ _).symm

end
end ManuscriptAudit.NodalSmoothLocusOverlap

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalSmoothLocusOverlap.smooth_charts_cover,
      ``ManuscriptAudit.NodalSmoothLocusOverlap.toPuncturedZ_toAffine,
      ``ManuscriptAudit.NodalSmoothLocusOverlap.smooth_parameter_pullback] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
