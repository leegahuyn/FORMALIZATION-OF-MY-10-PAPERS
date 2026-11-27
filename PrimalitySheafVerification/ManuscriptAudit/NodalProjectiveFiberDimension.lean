import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.TopologicalKrullDimensionOpenCover
import PrimalitySheafVerification.ManuscriptAudit.NodalAffineFiberDimension
import PrimalitySheafVerification.ManuscriptAudit.NodalChartIntersection
import PrimalitySheafVerification.ManuscriptAudit.IntegralOddPrimeFibers

/-! The proper nodal model and its canonical integral fibers have
Krull dimension one, including the actual point at infinity. -/

namespace ManuscriptAudit.NodalProjectiveFiberDimension

open AlgebraicGeometry CategoryTheory Scheme
open NodalProjectiveClosure (affineNode affineOpen projectiveNode)
open NodalProperYChart (chartOpen)
open NodalYChartImmersion (nodeYChart coordinateEquiv)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

variable (K : Type) [Field K]

private theorem affine_dimension : topologicalKrullDim (affineNode K) = 1 := by
  change topologicalKrullDim (PrimeSpectrum (NodalConductor.coordinates K)) = 1
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    NodalAffineFiberDimension.chart_ring_dimension K]

private theorem y_chart_dimension_le : topologicalKrullDim (nodeYChart K) ≤ 1 := by
  let q := (1 : Polynomial K) - Polynomial.X ^ 2
  let B := Localization.Away q
  let e : nodeYChart K ≅ Spec (CommRingCat.of B) :=
    Scheme.Spec.mapIso (coordinateEquiv K).symm.toRingEquiv.toCommRingCatIso.op
  have he := e.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq e.hom.homeomorph
  let j : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of (Polynomial K)) :=
    Spec.map (CommRingCat.ofHom (algebraMap (Polynomial K) B))
  letI : IsOpenImmersion j := IsOpenImmersion.of_isLocalization (S := B) q
  have hj := j.isOpenEmbedding.isInducing.topologicalKrullDim_le
  have hP : topologicalKrullDim (Spec (CommRingCat.of (Polynomial K))) = 1 := by
    change topologicalKrullDim (PrimeSpectrum (Polynomial K)) = 1
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
      ArithmeticLineModel.fiber_coordinate_dimension K]
  exact he.trans_le (hj.trans (le_of_eq hP))

private def chartScheme : Bool → Scheme.{0}
  | false => affineNode K
  | true => nodeYChart K

private def chartMap : ∀ b, chartScheme K b ⟶ projectiveNode K
  | false => affineOpen K
  | true => chartOpen K

private theorem chartMap_openImmersion (b : Bool) :
    IsOpenImmersion (chartMap K b) := by
  cases b
  · exact inferInstanceAs (IsOpenImmersion (affineOpen K))
  · exact inferInstanceAs (IsOpenImmersion (chartOpen K))

private theorem chart_points_cover (x : projectiveNode K) :
    ∃ b, ∃ y : chartScheme K b, chartMap K b y = x := by
  have h := congrArg (fun U : (projectiveNode K).Opens => (U : Set (projectiveNode K)))
    (NodalChartIntersection.charts_cover K)
  have hx : x ∈ Set.range (affineOpen K) ∪ Set.range (chartOpen K) := by
    change x ∈ (↑((affineOpen K).opensRange ⊔ (chartOpen K).opensRange) :
      Set (projectiveNode K))
    rw [h]
    trivial
  rcases hx with ⟨y, hy⟩ | ⟨y, hy⟩
  · exact ⟨false, y, hy⟩
  · exact ⟨true, y, hy⟩

private def chartOpenCover : (projectiveNode K).OpenCover where
  I₀ := Bool
  X := chartScheme K
  f := chartMap K
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    exact ⟨chart_points_cover K, chartMap_openImmersion K⟩

/-- Scheme Krull dimension of the full proper nodal cubic. -/
theorem dimension : topologicalKrullDim (projectiveNode K) = 1 := by
  apply le_antisymm
  · apply TopologicalKrullDimensionOpenCover.le_of_open_cover
      (fun b : Bool => (chartMap K b : chartScheme K b → projectiveNode K))
    · intro b
      cases b
      · exact (affineOpen K).isOpenEmbedding
      · exact (chartOpen K).isOpenEmbedding
    · exact chart_points_cover K
    · intro b
      cases b
      · exact (affine_dimension K).le
      · exact y_chart_dimension_le K
  · rw [← affine_dimension K]
    exact (affineOpen K).isOpenEmbedding.isInducing.topologicalKrullDim_le

private theorem y_chart_integral : IsIntegral (nodeYChart K) := by
  let q := (1 : Polynomial K) - Polynomial.X ^ 2
  have hq : q ≠ 0 := by
    intro h
    have h₂ := congrArg (fun p : Polynomial K => p.coeff 2) h
    have hOne : (1 : Polynomial K).coeff 2 = 0 := by
      rw [Polynomial.coeff_one, if_neg (by decide : (2 : ℕ) ≠ 0)]
    simp [q, hOne, Polynomial.coeff_X_pow] at h₂
  let B := Localization.Away q
  letI : IsDomain B := IsLocalization.Away.isDomain B hq
  let e : nodeYChart K ≅ Spec (CommRingCat.of B) :=
    Scheme.Spec.mapIso (coordinateEquiv K).symm.toRingEquiv.toCommRingCatIso.op
  exact IsIntegral.of_isIso e.inv

private theorem projective_irreducible : IrreducibleSpace (projectiveNode K) := by
  letI : IrreducibleSpace (affineNode K) :=
    inferInstanceAs (IrreducibleSpace (PrimeSpectrum (NodalConductor.coordinates K)))
  letI : IsDominant (affineOpen K) := NodalProjectiveClosure.affineOpen_isDominant K
  have hRange : IsIrreducible (Set.range (affineOpen K)) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ (affineNode K)).image _
      (affineOpen K).continuous.continuousOn
  have hClosure : closure (Set.range (affineOpen K)) = Set.univ :=
    dense_iff_closure_eq.mp (affineOpen K).denseRange
  rw [irreducibleSpace_def]
  change IsIrreducible (Set.univ : Set (projectiveNode K))
  rw [← hClosure]
  exact hRange.closure

/-- The full proper model is integral over every field. -/
theorem projective_integral : IsIntegral (projectiveNode K) := by
  let U := chartOpenCover K
  letI (i : U.I₀) : IsReduced (U.X i) := by
    change Bool at i
    change IsReduced (chartScheme K i)
    cases i
    · exact inferInstanceAs (IsReduced (affineNode K))
    · letI : IsIntegral (nodeYChart K) := y_chart_integral K
      exact inferInstanceAs (IsReduced (nodeYChart K))
  letI : IsReduced (projectiveNode K) := IsReduced.of_openCover U
  letI : IrreducibleSpace (projectiveNode K) := projective_irreducible K
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- All canonical closed-point fibers of the integral proper family
are one-dimensional, also in characteristic two. -/
theorem canonical_fiber_dimension (p : ℕ) [Fact p.Prime] :
    topologicalKrullDim (IntegralOddPrimeFibers.nodalFiber p) = 1 := by
  let e := IntegralOddPrimeFibers.nodeIso p
  exact (e.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq e.hom.homeomorph).trans
    (dimension (ZMod p))

end
end ManuscriptAudit.NodalProjectiveFiberDimension

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalProjectiveFiberDimension.dimension,
      ``ManuscriptAudit.NodalProjectiveFiberDimension.canonical_fiber_dimension,
      ``ManuscriptAudit.NodalProjectiveFiberDimension.projective_integral] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
