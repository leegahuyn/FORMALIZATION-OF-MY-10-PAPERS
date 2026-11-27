import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.IntegralNodalGeometricFiber
import PrimalitySheafVerification.ManuscriptAudit.NodalCompactSupportHZero
import PrimalitySheafVerification.ManuscriptAudit.NodalSmoothRationalBoundary
import PrimalitySheafVerification.ManuscriptAudit.SmoothLocusUnderIso

/-! The smooth locus of the canonical geometric nodal fibre omits precisely the actual rational node. -/

namespace ManuscriptAudit.IntegralNodalGeometricBoundary

open AlgebraicGeometry CategoryTheory
open IntegralNodalGeometricFiber
open NodalProjectiveClosure (projectiveNode projectiveNodeToBase)
open NodalSmoothRationalBoundary (projectiveOrigin projectiveOrigin_closed)
open NodalSmoothLocusOverlap (smoothOpen)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (p : ℕ) [Fact p.Prime]

abbrev geometricSmoothOpen := (geometricToBase p).smoothLocus

/-- The actual smooth loci are identified by the base-preserving geometric fibre isomorphism. -/
def geometricSmoothIso :
    (geometricSmoothOpen p).toScheme ≅ (smoothOpen (closureField p)).toScheme :=
  SmoothLocusUnderIso.iso (projectiveIso p) (geometricToBase p)
    (projectiveNodeToBase (closureField p)) (projectiveIso_over p)

/-- The rational point in the actual geometric fibre corresponding to the node in the plane model. -/
def origin : Spec (CommRingCat.of (closureField p)) ⟶ geometricFiber p :=
  projectiveOrigin (closureField p) ≫ (projectiveIso p).inv

theorem origin_closed : IsClosedImmersion (origin p) := by
  letI := projectiveOrigin_closed (closureField p)
  unfold origin
  infer_instance

private theorem origin_toModel :
    origin p ≫ (projectiveIso p).hom = projectiveOrigin (closureField p) := by
  rw [origin, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The actual relative smooth open is the complement of this closed rational point. -/
theorem geometric_smooth_range :
    Set.range (geometricSmoothOpen p).ι = (Set.range (origin p))ᶜ := by
  let e := projectiveIso p
  let g := projectiveNodeToBase (closureField p)
  have hs : e.hom ⁻¹ᵁ g.smoothLocus = (geometricToBase p).smoothLocus := by
    refine (e.hom.preimage_smoothLocus_eq g).trans ?_
    ext x
    simp only [Scheme.Hom.mem_smoothLocus, projectiveIso_over p]
  rw [Scheme.Opens.range_ι]
  ext x
  have hSm : x ∈ geometricSmoothOpen p ↔ e.hom x ∈ g.smoothLocus := by
    change x ∈ (geometricToBase p).smoothLocus ↔ _
    rw [← hs]
    exact e.hom.mem_preimage
  have hPoint (y : Spec (CommRingCat.of (closureField p))) :
      e.hom (origin p y) = projectiveOrigin (closureField p) y := by
    rw [← Scheme.Hom.comp_apply]
    exact congrArg (fun f : Spec (CommRingCat.of (closureField p)) ⟶
      projectiveNode (closureField p) ↦ f y) (origin_toModel p)
  have hPointMem : x ∈ Set.range (origin p) ↔
      e.hom x ∈ Set.range (projectiveOrigin (closureField p)) := by
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, (hPoint y).symm⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, e.hom.homeomorph.injective ((hPoint y).trans hy)⟩
  have hModel := Set.ext_iff.mp (NodalSmoothRationalBoundary.smooth_range (closureField p)) (e.hom x)
  rw [Scheme.Opens.range_ι, Set.mem_compl_iff] at hModel
  exact hSm.trans (hModel.trans (not_congr hPointMem).symm)

theorem geometric_preconnected : PreconnectedSpace (geometricFiber p) := by
  letI := NodalCompactSupportHZero.projectiveNode_irreducible (closureField p)
  let e := projectiveIso p
  have h : IsPreconnected (Set.univ : Set (projectiveNode (closureField p))) := isPreconnected_univ
  refine ⟨?_⟩
  have h' := h.image e.inv e.inv.continuous.continuousOn
  rwa [Set.image_univ, Set.range_eq_univ.mpr
    (show Function.Surjective e.inv from e.inv.homeomorph.surjective)] at h'

end
end ManuscriptAudit.IntegralNodalGeometricBoundary

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.IntegralNodalGeometricBoundary.geometricSmoothIso,
      ``ManuscriptAudit.IntegralNodalGeometricBoundary.origin_closed,
      ``ManuscriptAudit.IntegralNodalGeometricBoundary.geometric_smooth_range,
      ``ManuscriptAudit.IntegralNodalGeometricBoundary.geometric_preconnected] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
