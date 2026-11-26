import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalNormalizationFiber

/-! Coordinate comparison for the actual second projection of the split fiber. -/

namespace ManuscriptAudit.NodalNormalizationFiber

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (K : Type u) [Field K]

attribute [local instance] NodalMilnorCoefficients.originAlgebra

set_option synthInstance.maxHeartbeats 180000 in
set_option maxHeartbeats 1400000 in
/-- Under the scheme fiber identification, its second projection is
the morphism defined by evaluation on the two ordered branches. -/
theorem conductorFiberIso_second (h2 : (2 : K) ≠ 0) :
    (conductorFiberIso K h2).hom ≫ Spec.map (NodalConductorSquare.branches K) =
      pullback.snd (NodalAffineOrigin.originMap K) (affineNormalization K) := by
  let e := (tensor_isPullback K).isoPullback
  let i : Spec (CommRingCat.of (fiberRing K)) ≅ Spec (CommRingCat.of (K × K)) :=
    Scheme.Spec.mapIso (fiberRingEquiv K h2).symm.toCommRingCatIso.op
  have he : (conductorFiberIso K h2).hom = e.inv ≫ i.hom := rfl
  let d : CommRingCat.of (K × K) ⟶ CommRingCat.of (fiberRing K) :=
    (fiberRingEquiv K h2).symm.toCommRingCatIso.hom
  have hi : i.hom = Spec.map d := rfl
  have hp : e.hom ≫ pullback.snd (NodalAffineOrigin.originMap K) (affineNormalization K) =
      fiberSecond K := (tensor_isPullback K).isoPullback_hom_snd
  apply (cancel_epi e.hom).mp
  simp only [he, Category.assoc, Iso.hom_inv_id_assoc, hp, hi]
  rw [← Spec.map_comp]
  unfold fiberSecond
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro f
  change (fiberRingEquiv K h2).symm (f.eval 1, f.eval (-1)) = (1 ⊗ₜ[A K] f)
  apply (fiberRingEquiv K h2).injective
  rw [RingEquiv.apply_symm_apply, fiberRingEquiv_polynomial]

end
end ManuscriptAudit.NodalNormalizationFiber

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NodalNormalizationFiber.conductorFiberIso_second
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
