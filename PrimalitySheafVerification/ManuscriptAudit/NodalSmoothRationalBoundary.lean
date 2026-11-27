import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalAffineOrigin
import PrimalitySheafVerification.ManuscriptAudit.NodalSmoothLocusOverlap

/-! The geometric smooth open of the actual proper node omits exactly its rational singular point. -/

namespace ManuscriptAudit.NodalSmoothRationalBoundary

open AlgebraicGeometry CategoryTheory
open NodalProjectiveClosure (affineOpen affineOpen_toBase projectiveNode projectiveNodeToBase projectiveNode_isProper)
open NodalAffineOrigin (originMap originAlgebra originPoint)
open NodalSmoothLocus (nodePoint smoothLocus_eq_complement)
open NodalSmoothLocusOverlap (smoothOpen)

noncomputable section
universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type u) [Field K]

/-- The actual rational singular point, viewed in the proper closure. -/
def projectiveOrigin : Spec (CommRingCat.of K) ⟶ projectiveNode K :=
  originMap K ≫ affineOpen K

theorem projectiveOrigin_overBase :
    projectiveOrigin K ≫ projectiveNodeToBase K = 𝟙 (Spec (CommRingCat.of K)) := by
  let R := CommRingCat.of (NodalConductor.coordinates K)
  let a : CommRingCat.of K ⟶ R := CommRingCat.ofHom (algebraMap K (NodalConductor.coordinates K))
  let b : R ⟶ CommRingCat.of K := CommRingCat.ofHom (originAlgebra K).toRingHom
  have h : a ≫ b = 𝟙 (CommRingCat.of K) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    change originAlgebra K (algebraMap K (NodalConductor.coordinates K) x) = x
    exact ((originAlgebra K).commutes x).trans (Algebra.algebraMap_self_apply x)
  rw [projectiveOrigin, Category.assoc, affineOpen_toBase]
  change Spec.map b ≫ Spec.map a = _
  rw [← Spec.map_comp, h, Spec.map_id]

theorem projectiveOrigin_closed : IsClosedImmersion (projectiveOrigin K) := by
  letI := projectiveNode_isProper K
  letI : IsClosedImmersion (projectiveOrigin K ≫ projectiveNodeToBase K) := by
    rw [projectiveOrigin_overBase]
    infer_instance
  exact IsClosedImmersion.of_comp (projectiveOrigin K) (projectiveNodeToBase K)

private theorem origin_range : Set.range (projectiveOrigin K) = {nodePoint K} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    apply Set.mem_singleton_iff.mpr
    have hy : y = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    exact congrArg (projectiveOrigin K) hy
  · intro h
    obtain rfl := Set.mem_singleton_iff.mp h
    exact ⟨IsLocalRing.closedPoint K, rfl⟩

/-- The actual smooth open is exactly the complement of the rational singular support. -/
theorem smooth_range :
    Set.range (smoothOpen K).ι = (Set.range (projectiveOrigin K))ᶜ := by
  rw [Scheme.Opens.range_ι, smoothLocus_eq_complement, origin_range]

end
end ManuscriptAudit.NodalSmoothRationalBoundary

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalSmoothRationalBoundary.projectiveOrigin_overBase,
      ``ManuscriptAudit.NodalSmoothRationalBoundary.projectiveOrigin_closed,
      ``ManuscriptAudit.NodalSmoothRationalBoundary.smooth_range] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
