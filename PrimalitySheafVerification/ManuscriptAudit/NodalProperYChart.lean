import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalYChartImage

/-! The actual proper nodal curve contains both affine charts. The Y≠0
chart is the spectrum of the coordinate algebra with relation z=x²(x+z). -/

namespace ManuscriptAudit.NodalProperYChart

open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open CuspProperCompactification (affineZChartι standardZChartRing)
open CuspYChartAlgebra (grading plane y z X_mem_one yChartι)
open NodalProjectiveClosure (affineNode affineOpen projectiveNode nodeInPlane chartEvaluation
  chartEvaluation_surjective)
open NodalYChartImmersion (nodeYChart nodeToYChart nodeYInPlane nodeYInPlane_preimage_z
  xCoeff yCoordinateRing coordinateEquiv)
open NodalYChartImage (zKernel_yKernel)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 140000

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
variable (K : Type u) [Field K]

private instance : QuasiCompact (nodeYInPlane K) := quasiCompact_of_compactSpace _
private instance : QuasiCompact (nodeInPlane K) := quasiCompact_of_compactSpace _

private theorem imageIota_kernel_eq :
    (nodeInPlane K).imageι.ker = (nodeYInPlane K).imageι.ker := by
  change (nodeInPlane K).ker.subschemeι.ker = (nodeYInPlane K).ker.subschemeι.ker
  rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι,
    zKernel_yKernel]

private def imageIso : (nodeYInPlane K).image ≅ projectiveNode K :=
  letI := IsClosedImmersion.isIso_lift (nodeInPlane K).imageι (nodeYInPlane K).imageι
    (imageIota_kernel_eq K)
  asIso (IsClosedImmersion.lift (nodeInPlane K).imageι (nodeYInPlane K).imageι
    (imageIota_kernel_eq K).le)

/-- The native Y-chart of the proper projective nodal curve. -/
def chartOpen : nodeYChart K ⟶ projectiveNode K :=
  (nodeYInPlane K).toImage ≫ (imageIso K).hom

instance chartOpen_isOpenImmersion : IsOpenImmersion (chartOpen K) := by
  unfold chartOpen
  infer_instance

theorem chartOpen_inPlane : chartOpen K ≫ (nodeInPlane K).imageι = nodeYInPlane K := by
  unfold chartOpen imageIso
  simp only [Category.assoc, asIso_hom, IsClosedImmersion.lift_fac, Scheme.Hom.toImage_imageι]

def yOpen : (projectiveNode K).Opens :=
  (nodeInPlane K).imageι ⁻¹ᵁ Proj.basicOpen (grading K) (y K)

private theorem range_of_closed_chart {X U P : Type*}
    [TopologicalSpace U] [TopologicalSpace P] (f : X → U) (j : U → P)
    (hf : IsClosed (Set.range f)) (hj : Topology.IsEmbedding j) :
    Set.range (j ∘ f) = closure (Set.range (j ∘ f)) ∩ Set.range j := by
  rw [Set.range_comp]
  have h := hj.closure_eq_preimage_closure_image (Set.range f)
  rw [hf.closure_eq] at h
  calc
    j '' Set.range f = j '' (j ⁻¹' closure (j '' Set.range f)) :=
      congrArg (fun S : Set U => j '' S) h
    _ = _ := Set.image_preimage_eq_inter_range

private theorem opensRange_of_closed_ambient {A Q P : Scheme.{u}}
    (i : A ⟶ Q) [IsOpenImmersion i] (j : Q ⟶ P) [IsClosedImmersion j]
    (U : P.Opens) (h : Set.range (i ≫ j) = Set.range j ∩ (U : Set P)) :
    i.opensRange = j ⁻¹ᵁ U := by
  apply SetLike.coe_injective
  change Set.range i = j ⁻¹' (U : Set P)
  change Set.range (j ∘ i) = Set.range j ∩ (U : Set P) at h
  have hPre : j ⁻¹' Set.range (j ∘ i) = Set.range i := by
    rw [Set.range_comp, Set.preimage_image_eq _ j.isClosedEmbedding.injective]
  have hAll : j ⁻¹' Set.range j = Set.univ :=
    Set.eq_univ_of_forall (fun x => ⟨x, rfl⟩)
  rw [← hPre, h, Set.preimage_inter, hAll, Set.univ_inter]

private theorem nodeInPlane_range_closure :
    closure (Set.range (nodeInPlane K)) = Set.range (nodeInPlane K).imageι := by
  rw [← Scheme.Hom.support_ker]
  exact (Scheme.IdealSheafData.range_subschemeι _).symm

private theorem nodeYInPlane_range_closure :
    closure (Set.range (nodeYInPlane K)) = Set.range (nodeInPlane K).imageι := by
  rw [← Scheme.Hom.support_ker, ← zKernel_yKernel]
  exact (Scheme.IdealSheafData.range_subschemeι _).symm

set_option maxHeartbeats 240000 in
private theorem nodeYInPlane_range :
    Set.range (nodeYInPlane K) = Set.range (nodeInPlane K).imageι ∩
      (Proj.basicOpen (grading K) (y K) : Set (plane K)) := by
  let g := nodeToYChart K
  letI : IsClosedImmersion g := NodalYChartImmersion.nodeToYChart_closed K
  have h := range_of_closed_chart g (yChartι K) g.isClosedEmbedding.isClosed_range
    (yChartι K).isOpenEmbedding.isEmbedding
  change Set.range (nodeYInPlane K) =
    closure (Set.range (nodeYInPlane K)) ∩ Set.range (yChartι K) at h
  have hChart : Set.range (yChartι K) =
      (Proj.basicOpen (grading K) (y K) : Set (plane K)) :=
    congrArg (fun U : (plane K).Opens => (U : Set (plane K)))
      (Proj.opensRange_awayι (grading K) (y K) (X_mem_one K 1) (by decide))
  rw [nodeYInPlane_range_closure, hChart] at h
  exact h

set_option maxHeartbeats 240000 in
private theorem nodeInPlane_range :
    Set.range (nodeInPlane K) = Set.range (nodeInPlane K).imageι ∩
      (Proj.basicOpen (grading K) (z K) : Set (plane K)) := by
  let g : affineNode K ⟶ Spec (CommRingCat.of (standardZChartRing K)) :=
    Spec.map (CommRingCat.ofHom (chartEvaluation K))
  letI : IsClosedImmersion g :=
    IsClosedImmersion.spec_of_surjective _ (chartEvaluation_surjective K)
  have h := range_of_closed_chart g (affineZChartι K) g.isClosedEmbedding.isClosed_range
    (affineZChartι K).isOpenEmbedding.isEmbedding
  change Set.range (nodeInPlane K) =
    closure (Set.range (nodeInPlane K)) ∩ Set.range (affineZChartι K) at h
  have hChart : Set.range (affineZChartι K) =
      (Proj.basicOpen (grading K) (z K) : Set (plane K)) :=
    congrArg (fun U : (plane K).Opens => (U : Set (plane K)))
      (Proj.opensRange_awayι (grading K) (z K) (X_mem_one K 2) (by decide))
  rw [nodeInPlane_range_closure, hChart] at h
  exact h

theorem chartOpen_range : (chartOpen K).opensRange = yOpen K := by
  apply opensRange_of_closed_ambient (chartOpen K) (nodeInPlane K).imageι
  rw [chartOpen_inPlane]
  exact nodeYInPlane_range K

theorem affineOpen_range :
    (affineOpen K).opensRange = (nodeInPlane K).imageι ⁻¹ᵁ Proj.basicOpen (grading K) (z K) := by
  apply opensRange_of_closed_ambient (affineOpen K) (nodeInPlane K).imageι
  rw [affineOpen, Scheme.Hom.toImage_imageι]
  exact nodeInPlane_range K

/-- The Y-open subscheme is the spectrum of the actual Y-chart algebra. -/
def yOpenIsoChart : (yOpen K).toScheme ≅ nodeYChart K := by
  apply IsOpenImmersion.isoOfRangeEq (yOpen K).ι (chartOpen K)
  rw [Scheme.Opens.range_ι]
  change (yOpen K : Set (projectiveNode K)) = ((chartOpen K).opensRange : Set (projectiveNode K))
  rw [chartOpen_range]

/-- The open chart Y≠0 is the polynomial line with 1−x² inverted. -/
def yOpenIsoLocalizedPolynomial :
    (yOpen K).toScheme ≅
      Spec (CommRingCat.of (Localization.Away ((1 : Polynomial K) - Polynomial.X ^ 2))) :=
  (yOpenIsoChart K) ≪≫
    Scheme.Spec.mapIso (coordinateEquiv K).symm.toRingEquiv.toCommRingCatIso.op

/-- In the Y-chart coordinate, the overlap with Z≠0 is the principal open D(x). -/
theorem chartOpen_preimage_affine :
    (chartOpen K) ⁻¹ᵁ (affineOpen K).opensRange = PrimeSpectrum.basicOpen (xCoeff K) := by
  rw [affineOpen_range, ← Scheme.Hom.comp_preimage, chartOpen_inPlane, nodeYInPlane_preimage_z]

end
end ManuscriptAudit.NodalProperYChart

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalProperYChart.chartOpen_isOpenImmersion,
      ``ManuscriptAudit.NodalProperYChart.chartOpen_inPlane,
      ``ManuscriptAudit.NodalProperYChart.chartOpen_range,
      ``ManuscriptAudit.NodalProperYChart.affineOpen_range,
      ``ManuscriptAudit.NodalProperYChart.yOpenIsoChart,
      ``ManuscriptAudit.NodalProperYChart.yOpenIsoLocalizedPolynomial,
      ``ManuscriptAudit.NodalProperYChart.chartOpen_preimage_affine] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
