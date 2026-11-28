import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassInfinityChartImage

/-! The actual Y≠0 open of the proper Weierstrass closure is the literal Y=1 chart. -/

namespace ManuscriptAudit.WeierstrassProperInfinityChart

open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open CuspYChartAlgebra (grading plane y X_mem_one yChartι)
open WeierstrassInfinityChartImage (zKernel_yKernel)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra

universe u
variable {K : Type u} [Field K] (W : WeierstrassCurve.Affine K)

private instance : QuasiCompact (WeierstrassProjectiveClosure.inPlane W) :=
  quasiCompact_of_compactSpace _

private theorem imageIota_kernel_eq :
    (WeierstrassProjectiveClosure.inPlane W).imageι.ker = (WeierstrassInfinityChartImmersion.inPlane W).imageι.ker := by
  change (WeierstrassProjectiveClosure.inPlane W).ker.subschemeι.ker = (WeierstrassInfinityChartImmersion.inPlane W).ker.subschemeι.ker
  rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι,
    zKernel_yKernel]

private def imageIso : (WeierstrassInfinityChartImmersion.inPlane W).image ≅ WeierstrassProjectiveClosure.projectiveScheme W :=
  letI := IsClosedImmersion.isIso_lift (WeierstrassProjectiveClosure.inPlane W).imageι (WeierstrassInfinityChartImmersion.inPlane W).imageι
    (imageIota_kernel_eq W)
  asIso (IsClosedImmersion.lift (WeierstrassProjectiveClosure.inPlane W).imageι (WeierstrassInfinityChartImmersion.inPlane W).imageι
    (imageIota_kernel_eq W).le)

/-- The native Y-chart of the proper projective Weierstrass closure. -/
def chartOpen : WeierstrassInfinityChartImmersion.chartScheme W ⟶ WeierstrassProjectiveClosure.projectiveScheme W :=
  (WeierstrassInfinityChartImmersion.inPlane W).toImage ≫ (imageIso W).hom

instance chartOpen_isOpenImmersion : IsOpenImmersion (chartOpen W) := by
  unfold chartOpen
  infer_instance

theorem chartOpen_inPlane : chartOpen W ≫ (WeierstrassProjectiveClosure.inPlane W).imageι = WeierstrassInfinityChartImmersion.inPlane W := by
  unfold chartOpen imageIso
  simp only [Category.assoc, asIso_hom, IsClosedImmersion.lift_fac, Scheme.Hom.toImage_imageι]

def yOpen : (WeierstrassProjectiveClosure.projectiveScheme W).Opens :=
  (WeierstrassProjectiveClosure.inPlane W).imageι ⁻¹ᵁ Proj.basicOpen (grading K) (y K)

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

private theorem infinity_inPlane_range_closure :
    closure (Set.range (WeierstrassInfinityChartImmersion.inPlane W)) = Set.range (WeierstrassProjectiveClosure.inPlane W).imageι := by
  rw [← Scheme.Hom.support_ker, ← zKernel_yKernel]
  exact (Scheme.IdealSheafData.range_subschemeι _).symm

set_option maxHeartbeats 240000 in
private theorem infinity_inPlane_range :
    Set.range (WeierstrassInfinityChartImmersion.inPlane W) = Set.range (WeierstrassProjectiveClosure.inPlane W).imageι ∩
      (Proj.basicOpen (grading K) (y K) : Set (plane K)) := by
  let g := WeierstrassInfinityChartImmersion.toYChart W
  letI : IsClosedImmersion g := WeierstrassInfinityChartImmersion.toYChart_isClosedImmersion W
  have h := range_of_closed_chart g (yChartι K) g.isClosedEmbedding.isClosed_range
    (yChartι K).isOpenEmbedding.isEmbedding
  change Set.range (WeierstrassInfinityChartImmersion.inPlane W) =
    closure (Set.range (WeierstrassInfinityChartImmersion.inPlane W)) ∩ Set.range (yChartι K) at h
  have hChart : Set.range (yChartι K) =
      (Proj.basicOpen (grading K) (y K) : Set (plane K)) :=
    congrArg (fun U : (plane K).Opens => (U : Set (plane K)))
      (Proj.opensRange_awayι (grading K) (y K) (X_mem_one K 1) (by decide))
  rw [infinity_inPlane_range_closure, hChart] at h
  exact h

theorem chartOpen_range : (chartOpen W).opensRange = yOpen W := by
  apply opensRange_of_closed_ambient (chartOpen W) (WeierstrassProjectiveClosure.inPlane W).imageι
  rw [chartOpen_inPlane]
  exact infinity_inPlane_range W

/-- The Y-open subscheme is the spectrum of the actual Y-chart algebra. -/
def yOpenIsoChart : (yOpen W).toScheme ≅ WeierstrassInfinityChartImmersion.chartScheme W := by
  apply IsOpenImmersion.isoOfRangeEq (yOpen W).ι (chartOpen W)
  rw [Scheme.Opens.range_ι]
  change (yOpen W : Set (WeierstrassProjectiveClosure.projectiveScheme W)) = ((chartOpen W).opensRange : Set (WeierstrassProjectiveClosure.projectiveScheme W))
  rw [chartOpen_range]

end

end ManuscriptAudit.WeierstrassProperInfinityChart

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassProperInfinityChart.chartOpen_isOpenImmersion,
      ``ManuscriptAudit.WeierstrassProperInfinityChart.chartOpen_inPlane,
      ``ManuscriptAudit.WeierstrassProperInfinityChart.chartOpen_range,
      ``ManuscriptAudit.WeierstrassProperInfinityChart.yOpenIsoChart] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
