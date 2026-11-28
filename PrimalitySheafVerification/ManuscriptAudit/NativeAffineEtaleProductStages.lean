import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineEtaleRawStageElements
import PrimalitySheafVerification.ManuscriptAudit.NativeEtaleProductStageGluing

/-! A finite product of genuine affine stages is an actual affine
stage for the product chart. Maps from a common stage assemble
with the literal component identities. -/

namespace ManuscriptAudit.NativeAffineEtaleProductStages

open AlgebraicGeometry CategoryTheory
open AffineEtaleStageCategory (Stage hom)
open NativeAffineEtaleStageSections (etaleMap)
open NativeAffineEtaleRawStageElements (stageAfterMap)
open ProetaleAffineTensor (specMap)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A : Type u} [CommRing A] {ι : Type u} [Finite ι]
  (B : ι → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]

/-- The literal product of finitely many affine étale chart stages. -/
def productStage (T : ∀ i, Stage A (B i)) : Stage A (∀ i, B i) :=
  Stage.of A (∀ i, B i) <|
    AlgHom.pi (fun i ↦ (T i).toChart.comp (Pi.evalAlgHom A (fun j ↦ (T j).carrier) i))

/-- Restricting a product stage to a component refines to that
component's original stage by the actual coordinate projection. -/
def projectionStageMap (T : ∀ i, Stage A (B i)) (i : ι) :
    stageAfterMap (Pi.evalAlgHom A B i) (productStage B T) ⟶ T i :=
  ⟨Pi.evalAlgHom A (fun j ↦ (T j).carrier) i, rfl⟩

/-- A family of compatible maps across all charts assembles into
one map to their actual product stage. -/
def assemble {S : Stage A (∀ i, B i)} (T : ∀ i, Stage A (B i))
    (f : ∀ i, stageAfterMap (Pi.evalAlgHom A B i) S ⟶ T i) : S ⟶ productStage B T := by
  refine ⟨AlgHom.pi (fun i ↦ hom (f i)), ?_⟩
  apply AlgHom.ext
  intro x
  funext i
  exact DFunLike.congr_fun (f i).property x

set_option maxHeartbeats 2900000 in
/-- The two geometric component maps commute with the assembled
stage arrow on the actual small étale category. -/
theorem component_assemble {S : Stage A (∀ i, B i)} (T : ∀ i, Stage A (B i))
    (f : ∀ i, stageAfterMap (Pi.evalAlgHom A B i) S ⟶ T i) (i : ι) :
    NativeEtaleProductStageGluing.component (A := A) (fun j ↦ (T j).carrier) i ≫
        etaleMap (assemble B T f) = etaleMap (f i) := by
  apply MorphismProperty.Over.Hom.ext
  change specMap A (Pi.evalAlgHom A (fun j ↦ (T j).carrier) i) ≫
      specMap A (AlgHom.pi (fun j ↦ hom (f j))) = specMap A (hom (f i))
  rw [← Spec.map_comp] <;> rfl

end
end ManuscriptAudit.NativeAffineEtaleProductStages

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NativeAffineEtaleProductStages.projectionStageMap,
      ``ManuscriptAudit.NativeAffineEtaleProductStages.component_assemble] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
