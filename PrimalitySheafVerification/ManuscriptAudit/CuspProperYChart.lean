import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspYChartImage

/-!
# The second affine chart of the proper cusp

The (Y
e0) chart of the proper cusp is the line
([X:Y:Z]=[s:1:s^3]). Its overlap with the original affine cusp
is the connected nonempty open (D(s)).
-/

namespace ManuscriptAudit.CuspProperYChart

open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open CuspPunctured CuspProperCompactification CuspYChartAlgebra CuspYChartImage

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 512

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable (K : Type u) [Field K]

private theorem imageIota_kernel_eq :
    (cuspInPlane K).imageι.ker = (lineInPlane K).imageι.ker := by
  change (cuspInPlane K).ker.subschemeι.ker = (lineInPlane K).ker.subschemeι.ker
  rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι,
    cuspKernel_lineKernel]

private def imageIso : (lineInPlane K).image ≅ projectiveCusp K :=
  letI := IsClosedImmersion.isIso_lift (cuspInPlane K).imageι (lineInPlane K).imageι
    (imageIota_kernel_eq K)
  asIso (IsClosedImmersion.lift (cuspInPlane K).imageι (lineInPlane K).imageι
    (imageIota_kernel_eq K).le)

/-- The line as an actual open chart of the proper cusp. -/
def lineOpen : Spec (CommRingCat.of (Polynomial K)) ⟶ projectiveCusp K :=
  (lineInPlane K).toImage ≫ (imageIso K).hom

instance lineOpen_isOpenImmersion : IsOpenImmersion (lineOpen K) := by
  letI := lineInPlane_isImmersion K
  letI : QuasiCompact (lineInPlane K) := quasiCompact_of_compactSpace _
  unfold lineOpen
  infer_instance

theorem lineOpen_inPlane : lineOpen K ≫ (cuspInPlane K).imageι = lineInPlane K := by
  unfold lineOpen imageIso
  simp only [Category.assoc, asIso_hom, IsClosedImmersion.lift_fac, Scheme.Hom.toImage_imageι]

def yOpen : (projectiveCusp K).Opens :=
  (cuspInPlane K).imageι ⁻¹ᵁ Proj.basicOpen (grading K) (y K)

theorem lineOpen_range : (lineOpen K).opensRange = yOpen K := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    change ((lineOpen K) ≫ (cuspInPlane K).imageι) t ∈ Proj.basicOpen (grading K) (y K)
    rw [lineOpen_inPlane,
      ← Proj.opensRange_awayι (grading K) (y K) (X_mem_one K 1) (by decide)]
    exact ⟨Spec.map (CommRingCat.ofHom (evalYChart K)) t, rfl⟩
  · intro hx
    let g := Spec.map (CommRingCat.ofHom (evalYChart K))
    haveI : IsClosedImmersion g :=
      IsClosedImmersion.spec_of_surjective _ (evalYChart_surjective K)
    have hi : (cuspInPlane K).imageι x ∈ Set.range (yChartι K) := by
      change (cuspInPlane K).imageι x ∈ (yChartι K).opensRange
      rw [Proj.opensRange_awayι]
      exact hx
    obtain ⟨q, hq⟩ := hi
    have hClose : closure (Set.range (lineInPlane K)) = Set.range (cuspInPlane K).imageι := by
      letI : QuasiCompact (lineInPlane K) := quasiCompact_of_compactSpace _
      rw [← Scheme.Hom.support_ker, ← cuspKernel_lineKernel]
      exact (Scheme.IdealSheafData.range_subschemeι _).symm
    have hqClosure : yChartι K q ∈ closure (Set.range (lineInPlane K)) := by
      rw [hq, hClose]
      exact ⟨x, rfl⟩
    have hRange : Set.range (lineInPlane K) = (yChartι K) '' Set.range g := by
      change Set.range ((yChartι K) ∘ g) = _
      exact Set.range_comp _ _
    have he := (yChartι K).isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image
      (Set.range g)
    rw [g.isClosedEmbedding.isClosed_range.closure_eq, ← hRange] at he
    have hqImage : q ∈ Set.range g := by rw [he]; exact hqClosure
    obtain ⟨t, ht⟩ := hqImage
    refine ⟨t, (cuspInPlane K).imageι.isClosedEmbedding.injective ?_⟩
    calc
      _ = lineInPlane K t := by
        change ((lineOpen K) ≫ (cuspInPlane K).imageι) t = _
        rw [lineOpen_inPlane]
      _ = yChartι K q := by change yChartι K (g t) = _; rw [ht]
      _ = _ := hq

/-- The native open \(Y\ne0\) of the proper cusp is isomorphic to the affine line. -/
def yOpenIsoAffineLine : (yOpen K).toScheme ≅ Spec (CommRingCat.of (Polynomial K)) := by
  letI := lineOpen_isOpenImmersion K
  apply IsOpenImmersion.isoOfRangeEq (yOpen K).ι (lineOpen K)
  rw [Scheme.Opens.range_ι]
  change (yOpen K : Set (projectiveCusp K)) = ((lineOpen K).opensRange : Set (projectiveCusp K))
  rw [lineOpen_range]

theorem lineOpen_preimage_affine :
    (lineOpen K) ⁻¹ᵁ (affineOpen K).opensRange =
      PrimeSpectrum.basicOpen (Polynomial.X : Polynomial K) := by
  rw [affineOpen_opensRange_eq, ← Scheme.Hom.comp_preimage, lineOpen_inPlane, lineInPlane_preimage_z]

theorem affine_chart_cover :
    (affineOpen K).opensRange ⊔ (lineOpen K).opensRange = ⊤ := by
  apply top_unique
  intro p _
  change p ∈ (affineOpen K).opensRange ∨ p ∈ (lineOpen K).opensRange
  by_cases hp : p ∈ (affineOpen K).opensRange
  · exact Or.inl hp
  · right
    rw [lineOpen_range]
    exact (Proj.mem_basicOpen _ _ _).mpr (boundary_plane_coordinates K p hp).2.2

theorem affine_chart_overlap_isConnected :
    IsConnected ((((affineOpen K).opensRange ⊓ (lineOpen K).opensRange :
      (projectiveCusp K).Opens)) : Set (projectiveCusp K)) := by
  have hImage :
      (lineOpen K) '' ((lineOpen K) ⁻¹ᵁ (affineOpen K).opensRange :
        Set (Spec (CommRingCat.of (Polynomial K)))) =
        (((affineOpen K).opensRange ⊓ (lineOpen K).opensRange :
          (projectiveCusp K).Opens) : Set (projectiveCusp K)) := by
    exact Set.image_preimage_eq_inter_range
  rw [← hImage, lineOpen_preimage_affine]
  exact ((punctured_line_irreducible K).image _ (lineOpen K).continuous.continuousOn).isConnected

end

end ManuscriptAudit.CuspProperYChart

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CuspProperYChart.lineOpen_isOpenImmersion,
      ``ManuscriptAudit.CuspProperYChart.lineOpen_inPlane,
      ``ManuscriptAudit.CuspProperYChart.lineOpen_range,
      ``ManuscriptAudit.CuspProperYChart.yOpenIsoAffineLine,
      ``ManuscriptAudit.CuspProperYChart.lineOpen_preimage_affine,
      ``ManuscriptAudit.CuspProperYChart.affine_chart_cover,
      ``ManuscriptAudit.CuspProperYChart.affine_chart_overlap_isConnected] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
