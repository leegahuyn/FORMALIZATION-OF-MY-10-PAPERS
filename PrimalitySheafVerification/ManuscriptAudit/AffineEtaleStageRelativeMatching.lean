import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleStageAlgebraColimit
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineEtaleStageSmall
import PrimalitySheafVerification.ManuscriptAudit.AffineStageMatchingDescent
import PrimalitySheafVerification.ManuscriptAudit.AffineRelativeTensorMatchTransport
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
open AffineStageTensorCoproduct (tensorIso)
open AffineStageTensorLegs (algebraHom inl_tensorIso_hom inr_tensorIso_hom)
open AffineRelativeTensorMatchTransport (to_coproduct from_coproduct)
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
  [WeaklyEtale (structureMap B D)]

private abbrev R := CommRingCat.of B
private abbrev Q := CommRingCat.mkUnder (R (B := B)) (B ⊗[A] N)

private abbrev RelativeWitness (v : M →ₐ[A] D) (p q : M →ₐ[A] N) : Prop :=
  ∃ (T : Stage B D) (m : B ⊗[A] M →ₐ[B] T.carrier)
    (r : B ⊗[A] N →ₐ[B] T.carrier ⊗[B] T.carrier),
    T.toChart.comp m = extend (B := B) v ∧
      r.comp (extendMap (B := B) p) =
        (includeLeft : T.carrier →ₐ[B] T.carrier ⊗[B] T.carrier).comp m ∧
      r.comp (extendMap (B := B) q) =
        (includeRight : T.carrier →ₐ[B] T.carrier ⊗[B] T.carrier).comp m

set_option linter.unusedSectionVars false in
set_option maxHeartbeats 5800000 in
/-- A matching section's two actual stage maps to the limiting
tensor square can be represented with the same exact identities
on one genuine relative affine étale stage. -/
theorem exists_relative_stage (hApprox : FiniteTupleApproximation B D)
    (v : M →ₐ[A] D) (f : N →ₐ[A] D ⊗[B] D) (p q : M →ₐ[A] N)
    (hp : f.comp p = ((includeLeft : D →ₐ[B] D ⊗[B] D).restrictScalars A).comp v)
    (hq : f.comp q = ((includeRight : D →ₐ[B] D ⊗[B] D).restrictScalars A).comp v) :
    RelativeWitness (B := B) v p q := by
  letI : EssentiallySmall.{u} (Stage B D) := NativeAffineEtaleStageSmall.essentiallySmall_stage
  let i : Stage B D := Stage.of B D (extend (B := B) v)
  let D₀ : Stage B D ⥤ Under (R (B := B)) := algebraDiagram
  let c : Cocone D₀ := algebraCocone
  let w : CommRingCat.mkUnder (R (B := B)) (D ⊗[B] D) ≅ c.pt ⨿ c.pt :=
    tensorIso (R := R (B := B)) D D
  let t : Q (A := A) (B := B) (N := N) ⟶ c.pt ⨿ c.pt :=
    AlgHom.toUnder (R := R (B := B)) (extend (B := B) f) ≫ w.hom
  have hfpL : (extend (B := B) f).comp (extendMap (B := B) p) =
      (includeLeft : D →ₐ[B] D ⊗[B] D).comp (extend v) :=
    (extend_comp p f).trans ((congrArg (extend (B := B)) hp).trans
      (postcomp_extend v includeLeft).symm)
  have hfpR : (extend (B := B) f).comp (extendMap (B := B) q) =
      (includeRight : D →ₐ[B] D ⊗[B] D).comp (extend v) :=
    (extend_comp q f).trans ((congrArg (extend (B := B)) hq).trans
      (postcomp_extend v includeRight).symm)
  let l : D₀.obj i ⟶ Q (A := A) (B := B) (N := N) :=
    AlgHom.toUnder (R := R (B := B)) (extendMap (B := B) p)
  let r : D₀.obj i ⟶ Q (A := A) (B := B) (N := N) :=
    AlgHom.toUnder (R := R (B := B)) (extendMap (B := B) q)
  have hL : l ≫ t = c.ι.app i ≫ coprod.inl :=
    to_coproduct (extendMap (B := B) p) (extend (B := B) f) (extend (B := B) v)
      (includeLeft : D →ₐ[B] D ⊗[B] D) coprod.inl
      (inl_tensorIso_hom (R := B) (S := D) (T := D)) hfpL
  have hR : r ≫ t = c.ι.app i ≫ coprod.inr :=
    to_coproduct (extendMap (B := B) q) (extend (B := B) f) (extend (B := B) v)
      (includeRight : D →ₐ[B] D ⊗[B] D) coprod.inr
      (inr_tensorIso_hom (R := B) (S := D) (T := D)) hfpR
  have hPi : (D₀.obj i).hom.hom.FinitePresentation := by
    change (algebraMap B (B ⊗[A] M)).FinitePresentation
    exact RingHom.finitePresentation_algebraMap.mpr inferInstance
  have hPq : (Q (A := A) (B := B) (N := N)).hom.hom.FinitePresentation := by
    change (algebraMap B (B ⊗[A] N)).FinitePresentation
    exact RingHom.finitePresentation_algebraMap.mpr inferInstance
  have hc : IsColimit c := AffineEtaleStageAlgebraColimit.isColimit_algebra hApprox
  obtain ⟨j, ij, g, _, hlj, hrj⟩ :=
    AffineStageMatchingDescent.exists_match_at_stage (D := D₀) (c := c) hc i hPi
      (Q (A := A) (B := B) (N := N)) hPq l r t hL hR
  let z : CommRingCat.mkUnder (R (B := B)) (j.carrier ⊗[B] j.carrier) ≅
      D₀.obj j ⨿ D₀.obj j := tensorIso (R := R (B := B)) j.carrier j.carrier
  let e : B ⊗[A] N →ₐ[B] j.carrier ⊗[B] j.carrier := algebraHom (g ≫ z.inv)
  refine ⟨j, hom ij, e, ij.property, ?_, ?_⟩
  · exact from_coproduct (extendMap (B := B) p) g (hom ij)
      (includeLeft : j.carrier →ₐ[B] j.carrier ⊗[B] j.carrier) coprod.inl
      (inl_tensorIso_hom (R := B) (S := j.carrier) (T := j.carrier)) hlj
  · exact from_coproduct (extendMap (B := B) q) g (hom ij)
      (includeRight : j.carrier →ₐ[B] j.carrier ⊗[B] j.carrier) coprod.inr
      (inr_tensorIso_hom (R := B) (S := j.carrier) (T := j.carrier)) hrj

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
