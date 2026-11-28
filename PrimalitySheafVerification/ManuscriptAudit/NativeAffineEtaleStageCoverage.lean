import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineEtaleStageSections

/-! Every actual arrow from an affine weakly étale chart to an
affine étale object is represented by an actual affine étale stage. -/

namespace ManuscriptAudit.NativeAffineEtaleStageCoverage

open AlgebraicGeometry CategoryTheory Opposite
open ProetaleAffineTensor (spectrum structureMap specMap)
open NativeAffineEtaleStageSections (etaleObject chartArrow)
open AffineEtaleStageCategory (Stage)
open EtaleProetaleSiteInclusion (inclusion)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  [WeaklyEtale (structureMap A B)]

set_option maxHeartbeats 2600000 in
/-- Coordinates of an actual affine target identify its chart arrow
with the site arrow from the same actual affine étale stage. -/
theorem exists_stage (U : (spectrum A).Etale) [IsAffine U.left]
    (f : ProetaleAffineTensor.object A B ⟶ (inclusion (spectrum A)).obj U) :
    ∃ (T : Stage A B) (e : etaleObject T ≅ U),
      chartArrow T ≫ (inclusion (spectrum A)).map e.hom = f := by
  let C : CommRingCat.{u} := Scheme.Γ.obj (op U.left)
  let e : U.left ≅ Spec C := U.left.isoSpec
  let v := e.inv ≫ U.hom
  let φ : CommRingCat.of A ⟶ C := Spec.preimage v
  letI : Algebra A C := φ.hom.toAlgebra
  have hφ : structureMap A C = v := Spec.map_preimage v
  have hEt : Etale (structureMap A C) := by
    rw [hφ]
    change Etale (e.inv ≫ U.hom)
    infer_instance
  letI : Algebra.Etale A C := RingHom.etale_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Etale) (f := CommRingCat.ofHom (algebraMap A C))).mp hEt)
  let w := f.left ≫ e.hom
  let ψ : C ⟶ CommRingCat.of B := Spec.preimage w
  have hψ : Spec.map ψ = w := Spec.map_preimage w
  have hφψ : φ ≫ ψ = CommRingCat.ofHom (algebraMap A B) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ]
    change (f.left ≫ e.hom) ≫ structureMap A C = structureMap A B
    rw [hφ]
    change (f.left ≫ e.hom) ≫ e.inv ≫ U.hom = structureMap A B
    rw [Category.assoc, Iso.hom_inv_id_assoc]
    exact MorphismProperty.Over.w f
  let g : C →ₐ[A] B :=
    { toRingHom := ψ.hom
      commutes' := fun a ↦ RingHom.congr_fun (congrArg
        (fun m : CommRingCat.of A ⟶ CommRingCat.of B ↦ m.hom) hφψ) a }
  let T := Stage.of A B g
  let j : etaleObject T ≅ U := MorphismProperty.Over.isoMk e.symm hφ.symm
  refine ⟨T, j, ?_⟩
  apply MorphismProperty.Over.Hom.ext
  change specMap A g ≫ e.inv = f.left
  rw [show specMap A g = w from hψ]
  change (f.left ≫ e.hom) ≫ e.inv = f.left
  rw [Category.assoc, e.hom_inv_id, Category.comp_id]

end
end ManuscriptAudit.NativeAffineEtaleStageCoverage

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NativeAffineEtaleStageCoverage.exists_stage
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
