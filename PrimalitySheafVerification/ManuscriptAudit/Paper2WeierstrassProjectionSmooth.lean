import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper2WeierstrassReverseProjection

/-! The derivative charts are smooth over the ground ring, by their actual étale maps to affine lines. -/

namespace ManuscriptAudit.Paper2WeierstrassProjectionSmooth

open AlgebraicGeometry CategoryTheory Polynomial WeierstrassCurve

noncomputable section

variable {R : Type*} [CommRing R]

/-- The ordinary affine line is smooth over its ground ring. -/
theorem affineLine_smooth :
    Smooth (Spec.map (CommRingCat.ofHom (algebraMap R (Polynomial R)))) := by
  apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
  apply RingHom.smooth_algebraMap.mpr
  exact ⟨inferInstance, inferInstance⟩

theorem first_chart_smooth (W : WeierstrassCurve R) :
    Smooth (Spec.map (CommRingCat.ofHom
        (algebraMap (Polynomial R) (Paper2WeierstrassEtaleProjection.ProjectionChart W))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Polynomial R)))) := by
  letI := Paper2WeierstrassEtaleProjection.projection_scheme_etale W
  letI := affineLine_smooth (R := R)
  infer_instance

theorem second_chart_smooth (W : WeierstrassCurve R) :
    Smooth (Spec.map (CommRingCat.ofHom
        (algebraMap (Polynomial R) (Paper2WeierstrassReverseProjection.ReverseProjectionChart W))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Polynomial R)))) := by
  letI := Paper2WeierstrassReverseProjection.projection_scheme_etale W
  letI := affineLine_smooth (R := R)
  infer_instance

end
end ManuscriptAudit.Paper2WeierstrassProjectionSmooth

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper2WeierstrassProjectionSmooth.affineLine_smooth,
      ``ManuscriptAudit.Paper2WeierstrassProjectionSmooth.first_chart_smooth,
      ``ManuscriptAudit.Paper2WeierstrassProjectionSmooth.second_chart_smooth] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
