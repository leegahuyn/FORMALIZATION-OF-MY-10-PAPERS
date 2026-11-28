import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Pullbacks
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAffineTensor

/-! Surjectivity onto an actual affine chart passes through the
commuting factorization, and actual affine base change is the literal
tensor-product chart. -/

namespace ManuscriptAudit.AffineEtaleStageCoverGeometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ProetaleAffineTensor (spectrum structureMap specMap)
open scoped TensorProduct

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A B C D E : Type u}
  [CommRing A] [CommRing B] [CommRing C] [CommRing D] [CommRing E]
  [Algebra A B] [Algebra A C] [Algebra A D] [Algebra A E]

/-- An actual cover factoring through a pullback makes its projection
an actual surjection. -/
theorem pullback_surjective_of_factor
    (t : C →ₐ[A] B) (p : C →ₐ[A] E) (k : B →ₐ[A] D) (l : E →ₐ[A] D)
    (he : k.comp t = l.comp p) (hCov : Function.Surjective (specMap A k)) :
    Function.Surjective (pullback.fst (specMap A t) (specMap A p)) := by
  have h : specMap A k ≫ specMap A t = specMap A l ≫ specMap A p := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun m : C →ₐ[A] D ↦ specMap A m) he
  let g := pullback.lift (specMap A k) (specMap A l) h
  intro x
  obtain ⟨z, hz⟩ := hCov x
  refine ⟨g z, ?_⟩
  rw [← Scheme.Hom.comp_apply]
  exact (congrArg (fun m : ProetaleAffineTensor.spectrum D ⟶
    ProetaleAffineTensor.spectrum B ↦ m z) (pullback.lift_fst _ _ _)).trans hz

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T]

/-- A surjective actual first pullback projection is exactly the
surjective structural map of the affine base-change algebra. -/
theorem tensor_surjective
    (h : Function.Surjective (pullback.fst (structureMap R S) (structureMap R T))) :
    Function.Surjective (structureMap S (S ⊗[R] T)) := by
  let P := ProetaleAffineTensor.specTensor_isPullback R S T
  have hf : P.isoPullback.hom ≫ pullback.fst (structureMap R S) (structureMap R T) =
      structureMap S (S ⊗[R] T) := P.isoPullback_hom_fst
  have hi : P.isoPullback.inv ≫ structureMap S (S ⊗[R] T) =
      pullback.fst (structureMap R S) (structureMap R T) := by
    rw [← hf, P.isoPullback.inv_hom_id_assoc]
  intro x
  obtain ⟨p, hp⟩ := h x
  exact ⟨P.isoPullback.inv p, by simpa only [← Scheme.Hom.comp_apply, hi] using hp⟩

end
end ManuscriptAudit.AffineEtaleStageCoverGeometry

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleStageCoverGeometry.pullback_surjective_of_factor,
      ``ManuscriptAudit.AffineEtaleStageCoverGeometry.tensor_surjective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
