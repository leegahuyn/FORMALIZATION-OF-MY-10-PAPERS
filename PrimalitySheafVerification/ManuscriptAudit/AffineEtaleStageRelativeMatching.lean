import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleStageMatchPresentation
import PrimalitySheafVerification.ManuscriptAudit.AffineStageTensorExtensionMaps

/-! A finite stage witness for matching on an actual chart's
self-intersection descends to a genuine relative étale stage. -/

namespace ManuscriptAudit.AffineEtaleStageRelativeMatching

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ProetaleAffineTensor (structureMap)
open AffineEtaleStageMatchPresentation (RelativeWitness exists_match)
open AffineEtaleStageColimit (FiniteTupleApproximation)
open AffineStageTensorExtensionMaps (extend extendMap extend_comp postcomp_extend)
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

set_option maxHeartbeats 2600000 in
/-- A matching section's two actual stage maps to the limiting
tensor square can be represented with the same exact identities
on one genuine relative affine étale stage. -/
theorem exists_relative_stage (hApprox : FiniteTupleApproximation B D)
    (v : M →ₐ[A] D) (f : N →ₐ[A] D ⊗[B] D) (p q : M →ₐ[A] N)
    (hp : f.comp p = ((includeLeft : D →ₐ[B] D ⊗[B] D).restrictScalars A).comp v)
    (hq : f.comp q = ((includeRight : D →ₐ[B] D ⊗[B] D).restrictScalars A).comp v) :
    RelativeWitness (extend (B := B) v) (extendMap (B := B) p) (extendMap (B := B) q) := by
  have hL : (extend (B := B) f).comp (extendMap (B := B) p) =
      (includeLeft : D →ₐ[B] D ⊗[B] D).comp (extend v) :=
    (extend_comp p f).trans ((congrArg (extend (B := B)) hp).trans
      (postcomp_extend v includeLeft).symm)
  have hR : (extend (B := B) f).comp (extendMap (B := B) q) =
      (includeRight : D →ₐ[B] D ⊗[B] D).comp (extend v) :=
    (extend_comp q f).trans ((congrArg (extend (B := B)) hq).trans
      (postcomp_extend v includeRight).symm)
  exact exists_match hApprox (extend (B := B) v) (extend (B := B) f)
    (extendMap (B := B) p) (extendMap (B := B) q) hL hR

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
