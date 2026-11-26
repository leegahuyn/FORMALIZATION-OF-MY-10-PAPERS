import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspPatchedFiniteProjective
import PrimalitySheafVerification.ManuscriptAudit.MilnorIdentityRecovery

/-!
# The actual normalization scalar extension of the patched cusp algebra

The canonical normalization map is induced by the first projection of the
ring pullback. In basis coordinates it is the checked Milnor recovery map.
-/

namespace ManuscriptAudit.CuspNormalizationRecovery

open Polynomial
open CuspDelta CuspPunctured CuspEtaleConductorPatch CuspFiniteEtaleBases
open CuspMilnorCoefficients CuspPatchedFiniteProjective
open scoped TensorProduct

noncomputable section

universe u

variable (K : Type u) [Field K]
variable (E : Type u) [CommRing E] [Algebra (Polynomial K) E]
variable [Algebra.Etale (Polynomial K) E] [Module.Finite (Polynomial K) E]

private abbrev A := CuspSubalgebra K
private abbrev L := patchRing K E

local instance originAlgebra : Algebra (A K) K := (cuspOriginResidue K).toAlgebra

local instance descendedAlgebra : Algebra (A K) (L K E) := patchAlgebra K E


/-- The algebra map to the normalization induced by the actual first
projection of the conductor pullback. -/
def normalizationExtension :
    (Polynomial K ⊗[A K] L K E) →ₐ[Polynomial K] E :=
  Algebra.TensorProduct.lift (Algebra.ofId (Polynomial K) E) (firstProjection K E)
    (fun _ _ => Commute.all _ _)

set_option backward.isDefEq.respectTransparency false in
private theorem normalizationExtension_bijective :
    Function.Bijective (normalizationExtension K E) := by
  let q := quotientMap K
  let s := constantMap K
  let U := transitionMatrix K E
  let recover := MilnorNormalizationMap.normalizationMap q s U.val
  let toPatch := (patchModuleEquiv K E).baseChange (A K) (Polynomial K) _ _
  let coordinates := (normalizationBasis K E).2.equivFun
  have hSurj : Function.Surjective q := Ideal.Quotient.mk_surjective
  have hRecover : Function.Bijective recover :=
    MilnorIdentityRecovery.normalizationMap_bijective q s hSurj (pairMap_bijective K) U
  have hMap : coordinates.toLinearMap.comp (normalizationExtension K E).toLinearMap =
      recover.comp toPatch.toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro b x
    change coordinates (normalizationExtension K E (b ⊗ₜ[A K] x)) =
      b • ((patchModuleEquiv K E) x).val.1
    rw [normalizationExtension, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply]
    rw [← Algebra.smul_def, map_smul, patchModuleEquiv_fst] <;> rfl
  have hFunction : ⇑(normalizationExtension K E) = coordinates.symm ∘ recover ∘ toPatch := by
    funext x
    apply coordinates.injective
    change coordinates (normalizationExtension K E x) =
      coordinates (coordinates.symm (recover (toPatch x)))
    rw [LinearEquiv.apply_symm_apply]
    exact DFunLike.congr_fun hMap x
  rw [hFunction]
  exact coordinates.symm.bijective.comp (hRecover.comp toPatch.bijective)

/-- Scalar extension of the actual patched algebra to the polynomial
normalization recovers the original finite étale algebra. -/
def normalizationRecovery :
    (Polynomial K ⊗[A K] L K E) ≃ₐ[Polynomial K] E :=
  AlgEquiv.ofBijective (normalizationExtension K E) (normalizationExtension_bijective K E)

end

end ManuscriptAudit.CuspNormalizationRecovery

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CuspNormalizationRecovery.normalizationRecovery
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
