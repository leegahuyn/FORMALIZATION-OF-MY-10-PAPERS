import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleStageAlgebraColimit
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineEtaleStageSmall
import PrimalitySheafVerification.ManuscriptAudit.AffineStageMatchingDescent
import PrimalitySheafVerification.ManuscriptAudit.AffineStageTensorLegs
import PrimalitySheafVerification.ManuscriptAudit.AffineStageTensorExtensionMaps

/-! A finite stage witness for matching on an actual chart's
self-intersection descends to a genuine relative étale stage. -/

namespace ManuscriptAudit.AffineEtaleStageRelativeMatching

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ProetaleAffineTensor (structureMap)
open AffineEtaleStageCategory (Stage hom)
open AffineEtaleStageColimit (FiniteTupleApproximation)
open AffineEtaleStageAlgebraColimit (algebraCocone algebraDiagram)
open AffineStageTensorExtensionMaps (extend extendMap extend_comp postcomp_extend)
open AffineStageTensorCoproduct (tensorCofan tensorIso)
open AffineStageTensorLegs (algebraHom inl_tensorIso_hom inr_tensorIso_hom)
open Algebra.TensorProduct
open scoped TensorProduct

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A B D M N : Type u}
  [CommRing A] [CommRing B] [CommRing D] [CommRing M] [CommRing N]
  [Algebra A B] [Algebra A D] [Algebra A M] [Algebra A N] [Algebra B D]
  [IsScalarTower A B D] [Algebra.Etale A M] [Algebra.Etale A N]
  [Algebra A (D ⊗[B] D)] [IsScalarTower A B (D ⊗[B] D)]
  [WeaklyEtale (structureMap B D)]

private abbrev R := CommRingCat.of B
private abbrev Q := CommRingCat.mkUnder (R (B := B)) (B ⊗[A] N)

set_option maxHeartbeats 7000000 in
/-- A matching section's two actual stage maps to the limiting
tensor square can be represented with the same exact identities
on one genuine relative affine étale stage. -/
theorem exists_relative_stage (hApprox : FiniteTupleApproximation B D)
    (v : M →ₐ[A] D) (f : N →ₐ[A] D ⊗[B] D) (p q : M →ₐ[A] N)
    (hp : f.comp p = ((includeLeft : D →ₐ[B] D ⊗[B] D).restrictScalars A).comp v)
    (hq : f.comp q = ((includeRight : D →ₐ[B] D ⊗[B] D).restrictScalars A).comp v) :
    ∃ (T : Stage B D) (m : B ⊗[A] M →ₐ[B] T.carrier)
      (r : B ⊗[A] N →ₐ[B] T.carrier ⊗[B] T.carrier),
      T.toChart.comp m = extend v ∧
        r.comp (extendMap p) = (includeLeft : T.carrier →ₐ[B] _).comp m ∧
        r.comp (extendMap q) = (includeRight : T.carrier →ₐ[B] _).comp m := by
  letI : EssentiallySmall.{u} (Stage B D) := NativeAffineEtaleStageSmall.essentiallySmall_stage
  let i := Stage.of B D (extend (B := B) v)
  let c := algebraCocone (A := B) (B := D)
  let w := tensorIso (R := R (B := B)) D D
  let t := (extend (B := B) f).toUnder ≫ w.hom
  have hfpL : (extend (B := B) f).comp (extendMap (B := B) p) =
      (includeLeft : D →ₐ[B] D ⊗[B] D).comp (extend v) :=
    (extend_comp p f).trans ((congrArg (extend (B := B)) hp).trans
      (postcomp_extend v includeLeft).symm)
  have hfpR : (extend (B := B) f).comp (extendMap (B := B) q) =
      (includeRight : D →ₐ[B] D ⊗[B] D).comp (extend v) :=
    (extend_comp q f).trans ((congrArg (extend (B := B)) hq).trans
      (postcomp_extend v includeRight).symm)
  let l := (extendMap (B := B) p).toUnder
  let r := (extendMap (B := B) q).toUnder
  have hL : l ≫ t = c.ι.app i ≫ coprod.inl := by
    change (extendMap (B := B) p).toUnder ≫ ((extend (B := B) f).toUnder ≫ w.hom) =
      (extend (B := B) v).toUnder ≫ coprod.inl
    rw [← Category.assoc, ← AlgHom.toUnder_comp, hfpL, AlgHom.toUnder_comp, Category.assoc]
    exact congrArg (fun z ↦ (extend (B := B) v).toUnder ≫ z)
      (inl_tensorIso_hom (R := B) (S := D) (T := D))
  have hR : r ≫ t = c.ι.app i ≫ coprod.inr := by
    change (extendMap (B := B) q).toUnder ≫ ((extend (B := B) f).toUnder ≫ w.hom) =
      (extend (B := B) v).toUnder ≫ coprod.inr
    rw [← Category.assoc, ← AlgHom.toUnder_comp, hfpR, AlgHom.toUnder_comp, Category.assoc]
    exact congrArg (fun z ↦ (extend (B := B) v).toUnder ≫ z)
      (inr_tensorIso_hom (R := B) (S := D) (T := D))
  have hPi : ((algebraDiagram (A := B) (B := D)).obj i).hom.hom.FinitePresentation := by
    change (algebraMap B (B ⊗[A] M)).FinitePresentation
    exact RingHom.finitePresentation_algebraMap.mpr inferInstance
  have hPq : (Q (A := A) (B := B) (N := N)).hom.hom.FinitePresentation := by
    change (algebraMap B (B ⊗[A] N)).FinitePresentation
    exact RingHom.finitePresentation_algebraMap.mpr inferInstance
  obtain ⟨j, ij, g, _, hlj, hrj⟩ := AffineStageMatchingDescent.exists_match_at_stage
    (AffineEtaleStageAlgebraColimit.isColimit_algebra hApprox) i hPi _ hPq l r t hL hR
  let z := tensorIso (R := R (B := B)) j.carrier j.carrier
  let e : B ⊗[A] N →ₐ[B] j.carrier ⊗[B] j.carrier := algebraHom (g ≫ z.inv)
  refine ⟨j, hom ij, e, ij.property, ?_, ?_⟩
  · apply AlgHom.ext
    intro x
    have h := congrArg (fun h ↦ h ≫ z.inv) hlj
    have hLeg : coprod.inl ≫ z.inv =
        (tensorCofan (R := R (B := B)) j.carrier j.carrier).inl := by
      rw [← inl_tensorIso_hom (R := B) (S := j.carrier) (T := j.carrier)]
      rw [Category.assoc, z.hom_inv_id, Category.comp_id]
    rw [Category.assoc, Category.assoc, hLeg] at h
    exact congrArg (fun a ↦ a.right x) h
  · apply AlgHom.ext
    intro x
    have h := congrArg (fun h ↦ h ≫ z.inv) hrj
    have hLeg : coprod.inr ≫ z.inv =
        (tensorCofan (R := R (B := B)) j.carrier j.carrier).inr := by
      rw [← inr_tensorIso_hom (R := B) (S := j.carrier) (T := j.carrier)]
      rw [Category.assoc, z.hom_inv_id, Category.comp_id]
    rw [Category.assoc, Category.assoc, hLeg] at h
    exact congrArg (fun a ↦ a.right x) h

end
end ManuscriptAudit.AffineEtaleStageRelativeMatching

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineEtaleStageRelativeMatching.exists_relative_stage
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
