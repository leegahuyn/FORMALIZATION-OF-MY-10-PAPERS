import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalSmoothMobiusTransition
import PrimalitySheafVerification.ManuscriptAudit.TwoOpenSchemeGlue

/-! The native smooth locus of the proper nodal cubic is the actual
multiplicative group, by Möbius gluing along the computed overlap. -/

namespace ManuscriptAudit.NodalSmoothLocusGm

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NodalSmoothLocusOverlap (smoothScheme puncturedZ puncturedZRing zSmooth ySmooth
  smooth_charts_cover toPuncturedZ smooth_parameter_pullback)
open NodalSmoothMobiusGm (Gm laurentRing minusRing minusOpen minusInGm
  uMinusOne uMinusOne_laurent nodalPunctureIsoMinusOpen)
open NodalSmoothMobiusY (plusRing plusOpen plusInGm uPlusOne uPlusOne_laurent
  nodalYIsoPlusOpen yMobiusEquiv)
open NodalSmoothMobiusTransition (laurentToZ laurentToY laurent_maps_agree yGenerator_relation)
open NodalAwayNormalization (normalizationEquiv)
open NodalSmoothMobius (mobiusEquiv)
open NodalYChartImmersion (nodeYChart yCoordinateRing xCoeff zCoeff yRing_coefficient_inverse)
open NodalProjectiveClosure (affineOpen)
open NodalProperYChart (chartOpen)
open NodalChartIntersection (intersectionIsoParameter intersectionIsoParameter_inv_snd
  intersection_snd_opensRange)
open NodalYChartOverlapPlane (parameterScheme toNodeYChart)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (K : Type u) [Field K]

def zGm (h2 : (2 : K) ≠ 0) : puncturedZ K ⟶ Gm K :=
  Spec.map (CommRingCat.ofHom (laurentToZ K h2).toRingHom)

def yGm (h2 : (2 : K) ≠ 0) : nodeYChart K ⟶ Gm K :=
  Spec.map (CommRingCat.ofHom (laurentToY K h2).toRingHom)

private theorem minusOpen_fac :
    (NodalSmoothMobiusGm.localizationOpenIso K).hom ≫ (minusOpen K).ι = minusInGm K :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

private theorem plusOpen_fac :
    (NodalSmoothMobiusY.localizationOpenIso K).hom ≫ (plusOpen K).ι = plusInGm K :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

private theorem zGm_as_open (h2 : (2 : K) ≠ 0) :
    zGm K h2 = (nodalPunctureIsoMinusOpen K h2).hom ≫ (minusOpen K).ι := by
  simp only [nodalPunctureIsoMinusOpen, Iso.trans_hom, Category.assoc]
  change Spec.map (CommRingCat.ofHom (laurentToZ K h2).toRingHom) =
    Spec.map (CommRingCat.ofHom (normalizationEquiv K).symm.toAlgHom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (mobiusEquiv K h2).symm.toAlgHom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (NodalSmoothMobiusGm.localizationEquiv K).symm.toAlgHom.toRingHom) ≫
          (NodalSmoothMobiusGm.localizationOpenIso K).hom ≫ (minusOpen K).ι
  simp only [minusOpen_fac, minusInGm, ← Spec.map_comp] <;> rfl

private theorem yGm_as_open (h2 : (2 : K) ≠ 0) :
    yGm K h2 = (nodalYIsoPlusOpen K h2).hom ≫ (plusOpen K).ι := by
  simp only [nodalYIsoPlusOpen, Iso.trans_hom, Category.assoc]
  change Spec.map (CommRingCat.ofHom (laurentToY K h2).toRingHom) =
    Spec.map (CommRingCat.ofHom (yMobiusEquiv K h2).symm.toAlgHom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (NodalSmoothMobiusY.localizationEquiv K).symm.toAlgHom.toRingHom) ≫
        (NodalSmoothMobiusY.localizationOpenIso K).hom ≫ (plusOpen K).ι
  simp only [plusOpen_fac, plusInGm, ← Spec.map_comp] <;> rfl

instance zGm_open (h2 : (2 : K) ≠ 0) : IsOpenImmersion (zGm K h2) := by
  rw [zGm_as_open]
  infer_instance

instance yGm_open (h2 : (2 : K) ≠ 0) : IsOpenImmersion (yGm K h2) := by
  rw [yGm_as_open]
  infer_instance

theorem zGm_range (h2 : (2 : K) ≠ 0) : (zGm K h2).opensRange = minusOpen K := by
  apply SetLike.coe_injective
  change Set.range (zGm K h2) = (minusOpen K : Set (Gm K))
  rw [zGm_as_open]
  change (↑(((nodalPunctureIsoMinusOpen K h2).hom ≫ (minusOpen K).ι).opensRange) :
    Set (Gm K)) = _
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  exact Scheme.Opens.range_ι _

theorem yGm_range (h2 : (2 : K) ≠ 0) : (yGm K h2).opensRange = plusOpen K := by
  apply SetLike.coe_injective
  change Set.range (yGm K h2) = (plusOpen K : Set (Gm K))
  rw [yGm_as_open]
  change (↑(((nodalYIsoPlusOpen K h2).hom ≫ (plusOpen K).ι).opensRange) :
    Set (Gm K)) = _
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  exact Scheme.Opens.range_ι _

private theorem two_unit {R : Type u} [CommRing R] [Algebra K R]
    (h2 : (2 : K) ≠ 0) : IsUnit (2 : R) := by
  let f := algebraMap K R
  have hf : f (2 : K) = (2 : R) := by
    have h : f ((1 : K) + 1) = (1 : R) + 1 :=
      (f.map_add 1 1).trans (congrArg₂ (· + ·) f.map_one f.map_one)
    simpa only [one_add_one_eq_two] using h
  rw [← hf]
  exact (isUnit_iff_ne_zero.mpr h2).map f

private theorem basicOpen_unit {R : Type u} [CommRing R] {r : R} (h : IsUnit r) :
    PrimeSpectrum.basicOpen r = ⊤ := by
  obtain ⟨s, h⟩ := isUnit_iff_exists_inv.mp h
  have hm := PrimeSpectrum.basicOpen_mul r s
  rw [h, PrimeSpectrum.basicOpen_one] at hm
  exact top_unique (hm.le.trans inf_le_left)

private theorem sPlusOne_unit : IsUnit (xCoeff K + 1) := by
  have h : IsUnit (1 - xCoeff K ^ 2) :=
    isUnit_iff_exists_inv.mpr ⟨1 + xCoeff K ^ 2 + xCoeff K * zCoeff K,
      yRing_coefficient_inverse K⟩
  rw [show 1 - xCoeff K ^ 2 = (1 - xCoeff K) * (xCoeff K + 1) by ring] at h
  exact (IsUnit.mul_iff.mp h).2

private theorem coordinate_minus_relation (h2 : (2 : K) ≠ 0) :
    laurentToY K h2 (uMinusOne K) * (xCoeff K + 1) =
      -(2 : yCoordinateRing K) * xCoeff K := by
  rw [uMinusOne_laurent, map_sub, map_one]
  calc
    _ = laurentToY K h2 (LaurentPolynomial.T 1) * (xCoeff K + 1) - (xCoeff K + 1) := by ring
    _ = _ := by rw [yGenerator_relation]; ring

theorem yGm_preimage_z (h2 : (2 : K) ≠ 0) :
    (yGm K h2) ⁻¹ᵁ (zGm K h2).opensRange = PrimeSpectrum.basicOpen (xCoeff K) := by
  rw [zGm_range, yGm, minusOpen, SpecMap_preimage_basicOpen]
  change PrimeSpectrum.basicOpen (laurentToY K h2 (uMinusOne K)) = _
  calc
    _ = PrimeSpectrum.basicOpen (laurentToY K h2 (uMinusOne K) * (xCoeff K + 1)) := by
      rw [PrimeSpectrum.basicOpen_mul, basicOpen_unit (sPlusOne_unit K), inf_top_eq]
    _ = _ := by
      rw [coordinate_minus_relation, PrimeSpectrum.basicOpen_mul,
        basicOpen_unit ((two_unit K h2 : IsUnit (2 : yCoordinateRing K)).neg), top_inf_eq]

theorem gm_charts_cover (h2 : (2 : K) ≠ 0) :
    Set.range (zGm K h2) ∪ Set.range (yGm K h2) = Set.univ := by
  have h : (zGm K h2).opensRange ⊔ (yGm K h2).opensRange = ⊤ := by
    rw [zGm_range, yGm_range]
    apply top_unique
    intro p _
    change p ∈ PrimeSpectrum.basicOpen (uMinusOne K) ∨ p ∈ PrimeSpectrum.basicOpen (uPlusOne K)
    by_cases hm : uMinusOne K ∈ p.asIdeal
    · right
      apply (PrimeSpectrum.mem_basicOpen _ _).mpr
      intro hp
      have hd : uPlusOne K - uMinusOne K = (2 : laurentRing K) := by
        rw [uPlusOne_laurent, uMinusOne_laurent]
        ring
      have h₂ : (2 : laurentRing K) ∈ p.asIdeal := hd ▸ p.asIdeal.sub_mem hp hm
      obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp (two_unit K h2 : IsUnit (2 : laurentRing K))
      exact p.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr (hv ▸ p.asIdeal.mul_mem_right v h₂))
    · exact Or.inl ((PrimeSpectrum.mem_basicOpen _ _).mpr hm)
  exact congrArg (fun W : (Gm K).Opens => (W : Set (Gm K))) h

private theorem gmOverlap_square (h2 : (2 : K) ≠ 0) :
    toPuncturedZ K ≫ zGm K h2 = toNodeYChart K ≫ yGm K h2 := by
  unfold toPuncturedZ zGm toNodeYChart yGm
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext
    (congrArg AlgHom.toRingHom (laurent_maps_agree K h2)))

private instance parameterToY_open : IsOpenImmersion (toNodeYChart K) := by
  rw [← intersectionIsoParameter_inv_snd]
  infer_instance

private theorem parameterToY_range :
    (toNodeYChart K).opensRange = PrimeSpectrum.basicOpen (xCoeff K) := by
  apply SetLike.coe_injective
  change Set.range (toNodeYChart K) = (PrimeSpectrum.basicOpen (xCoeff K)).1
  rw [← intersectionIsoParameter_inv_snd]
  change (↑(((intersectionIsoParameter K).inv ≫
    pullback.snd (affineOpen K) (chartOpen K)).opensRange) : Set (nodeYChart K)) = _
  rw [Scheme.Hom.opensRange_comp_of_isIso, intersection_snd_opensRange] <;> rfl

private theorem gmSnd_range (h2 : (2 : K) ≠ 0) :
    (pullback.snd (zGm K h2) (yGm K h2)).opensRange = PrimeSpectrum.basicOpen (xCoeff K) := by
  rw [Scheme.Hom.opensRange_pullbackSnd, yGm_preimage_z]

private def gmParameterIso (h2 : (2 : K) ≠ 0) :
    parameterScheme K ≅ pullback (zGm K h2) (yGm K h2) :=
  IsOpenImmersion.isoOfRangeEq (toNodeYChart K) (pullback.snd (zGm K h2) (yGm K h2))
    (congrArg (fun W : (nodeYChart K).Opens => (W : Set (nodeYChart K)))
      ((parameterToY_range K).trans (gmSnd_range K h2).symm))

private theorem gmParameterIso_snd (h2 : (2 : K) ≠ 0) :
    (gmParameterIso K h2).hom ≫ pullback.snd (zGm K h2) (yGm K h2) = toNodeYChart K :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

private theorem gmParameterIso_fst (h2 : (2 : K) ≠ 0) :
    (gmParameterIso K h2).hom ≫ pullback.fst (zGm K h2) (yGm K h2) = toPuncturedZ K := by
  apply (cancel_mono (zGm K h2)).mp
  rw [Category.assoc, pullback.condition, ← Category.assoc, gmParameterIso_snd, gmOverlap_square]

/-- The smooth-locus scheme is Gm over any field where the node has two distinct branches. -/
def smoothLocusIsoGm (h2 : (2 : K) ≠ 0) : smoothScheme K ≅ Gm K := by
  let h := smooth_parameter_pullback K
  let e := h.isoPullback.symm ≪≫ gmParameterIso K h2
  refine TwoOpenSchemeGlue.isoOfIntersections (zSmooth K) (ySmooth K) (zGm K h2) (yGm K h2)
    (smooth_charts_cover K) (gm_charts_cover K h2) e ?_ ?_
  · change (h.isoPullback.inv ≫ (gmParameterIso K h2).hom) ≫
      pullback.fst (zGm K h2) (yGm K h2) = _
    rw [Category.assoc, gmParameterIso_fst]
    exact h.isoPullback_inv_fst
  · change (h.isoPullback.inv ≫ (gmParameterIso K h2).hom) ≫
      pullback.snd (zGm K h2) (yGm K h2) = _
    rw [Category.assoc, gmParameterIso_snd]
    exact h.isoPullback_inv_snd

/-- Under the actual smooth-locus isomorphism, the Y-chart is its displayed
open subspace of the multiplicative group. -/
theorem ySmooth_comp_iso (h2 : (2 : K) ≠ 0) :
    ySmooth K ≫ (smoothLocusIsoGm K h2).hom = yGm K h2 := by
  unfold smoothLocusIsoGm
  apply TwoOpenSchemeGlue.isoOfIntersections_hom_right

/-- The coordinate isomorphism from the literal Y-chart to the principal localization. -/
def yChartIsoPrincipal (h2 : (2 : K) ≠ 0) :
    nodeYChart K ≅ Spec (CommRingCat.of (plusRing K)) :=
  (Scheme.Spec.mapIso (yMobiusEquiv K h2).toRingEquiv.toCommRingCatIso.op).symm ≪≫
    (Scheme.Spec.mapIso (NodalSmoothMobiusY.localizationEquiv K).toRingEquiv.toCommRingCatIso.op).symm

/-- The principal localization inclusion is the actual morphism on the Y-chart. -/
theorem yChartIsoPrincipal_comp (h2 : (2 : K) ≠ 0) :
    (yChartIsoPrincipal K h2).hom ≫ plusInGm K = yGm K h2 := by
  rw [yGm_as_open, ← plusOpen_fac]
  simp only [yChartIsoPrincipal, nodalYIsoPlusOpen, Iso.trans_hom, Category.assoc]

end
end ManuscriptAudit.NodalSmoothLocusGm

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalSmoothLocusGm.yGm_preimage_z,
      ``ManuscriptAudit.NodalSmoothLocusGm.gm_charts_cover,
      ``ManuscriptAudit.NodalSmoothLocusGm.smoothLocusIsoGm,
      ``ManuscriptAudit.NodalSmoothLocusGm.ySmooth_comp_iso,
      ``ManuscriptAudit.NodalSmoothLocusGm.yChartIsoPrincipal_comp] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"

