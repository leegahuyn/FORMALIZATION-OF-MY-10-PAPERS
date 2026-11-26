import Lean.Util.CollectAxioms
import Mathlib.Algebra.Ring.Fin
import Mathlib.RingTheory.Etale.Pi
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Spectrum.Prime.Topology
import PrimalitySheafVerification.ManuscriptAudit.EtaleOfSurjectiveSpecBaseChange
import PrimalitySheafVerification.ManuscriptAudit.NodalNormalization
import PrimalitySheafVerification.ManuscriptAudit.NodalSwapCoverPatch

/-!
# The actual crossed algebra is a finite étale cover

The scalar extension to the surjective normalization is the product of
two polynomial rings, as an algebra. Finite projectivity and the
finite presentation then descend étaleness to the split node.
-/

namespace ManuscriptAudit.NodalSwapCoverEtale

open NodalConductor NodalMilnorCoefficients NodalSwapCover NodalSwapCoverPatch Polynomial
open scoped TensorProduct

noncomputable section

universe u

variable (K : Type u) [Field K]

private abbrev A := coordinates K
private abbrev B := Polynomial K
private abbrev E := (B K) × (B K)

local instance : Algebra (A K) K := originAlgebra K

local instance : IsScalarTower (A K) (B K) (E K) where
  smul_assoc a b z := Prod.ext (smul_assoc a b z.1) (smul_assoc a b z.2)

def normalizationExtension : (B K ⊗[A K] Cover K) →ₐ[B K] E K :=
  Algebra.TensorProduct.lift (Algebra.ofId (B K) (E K)) (polynomialProjection K)
    (fun _ _ => Commute.all _ _)

set_option backward.isDefEq.respectTransparency false in
private theorem normalizationExtension_bijective (h2 : (2 : K) ≠ 0) :
    Function.Bijective (normalizationExtension K) := by
  let recover := MilnorNormalizationMap.normalizationMap (branchMap K) (residueMap K)
    (transition K).val
  let toPatch := (patchEquiv K).baseChange (A K) (B K) (Cover K) (SwapPatch K)
  let vector := (LinearEquiv.finTwoArrow (B K) (B K)).symm
  have hRecover : Function.Bijective recover :=
    NodalMilnorCoefficients.normalizationMap_bijective K (Fin 2) h2 (transition K)
  have hMap : vector.toLinearMap.comp (normalizationExtension K).toLinearMap =
      recover.comp toPatch.toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro b z
    change vector (normalizationExtension K (b ⊗ₜ[A K] z)) = b • (patchEquiv K z).val.1
    rw [normalizationExtension, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply]
    rw [← Algebra.smul_def, map_smul, patchEquiv_fst] <;> rfl
  have hFun : ⇑(normalizationExtension K) = vector.symm ∘ recover ∘ toPatch := by
    funext z
    apply vector.injective
    change vector (normalizationExtension K z) = vector (vector.symm (recover (toPatch z)))
    rw [LinearEquiv.apply_symm_apply]
    exact DFunLike.congr_fun hMap z
  rw [hFun]
  exact vector.symm.bijective.comp (hRecover.comp toPatch.bijective)

/-- The actual finite cover is split as an algebra over the normalization. -/
def normalizationRecovery (h2 : (2 : K) ≠ 0) : (B K ⊗[A K] Cover K) ≃ₐ[B K] E K :=
  AlgEquiv.ofBijective (normalizationExtension K) (normalizationExtension_bijective K h2)

private def productFunctions : E K ≃ₐ[B K] (Fin 2 → B K) :=
  { (RingEquiv.piFinTwo (fun _ : Fin 2 => B K)).symm with
    commutes' := by
      intro b
      funext i
      fin_cases i <;> rfl }

private theorem normalization_is_surjective (h2 : (2 : K) ≠ 0) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap (A K) (B K))) := by
  letI : Module.Finite (A K) (B K) := NodalNormalization.normalization_finite K h2
  letI : FaithfulSMul (A K) (B K) :=
    (faithfulSMul_iff_algebraMap_injective (A K) (B K)).mpr Subtype.val_injective
  exact Algebra.IsIntegral.comap_surjective (A K) (B K)

private theorem node_isNoetherian : IsNoetherianRing (A K) := by
  letI : Algebra.FiniteType K (A K) := by
    change Algebra.FiniteType K (Algebra.adjoin K ({x K, y K} : Set K[X]))
    exact Algebra.FiniteType.adjoin_of_finite ((Set.finite_singleton _).insert _)
  exact Algebra.FiniteType.isNoetherianRing K (A K)

theorem cover_finite_etale (h2 : (2 : K) ≠ 0) :
    Module.Finite (A K) (Cover K) ∧ Algebra.Etale (A K) (Cover K) := by
  obtain ⟨hFin, hProj⟩ := cover_finite_projective K h2
  letI := hFin
  letI := hProj
  letI : Module.Flat (A K) (Cover K) := inferInstance
  letI : IsNoetherianRing (A K) := node_isNoetherian K
  letI : Algebra.FinitePresentation (A K) (Cover K) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  letI : Algebra.Etale (B K) (E K) := Algebra.Etale.of_equiv (productFunctions K).symm
  letI : Algebra.Etale (B K) (B K ⊗[A K] Cover K) :=
    Algebra.Etale.of_equiv (normalizationRecovery K h2).symm
  exact ⟨hFin, EtaleOfSurjectiveSpecBaseChange.etale_of_tensor_etale
    (A K) (B K) (Cover K) (normalization_is_surjective K h2)⟩

/-- The finite étale morphism is onto the actual affine node. -/
theorem cover_spec_surjective (h2 : (2 : K) ≠ 0) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap (A K) (Cover K))) := by
  letI : Module.Finite (A K) (Cover K) := (cover_finite_etale K h2).1
  letI : FaithfulSMul (A K) (Cover K) :=
    (faithfulSMul_iff_algebraMap_injective (A K) (Cover K)).mpr fun a b h =>
      Subtype.ext (congrArg (fun z : Cover K => z.val.1) h)
  exact Algebra.IsIntegral.comap_surjective (A K) (Cover K)

end

end ManuscriptAudit.NodalSwapCoverEtale

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in
      [``ManuscriptAudit.NodalSwapCoverEtale.normalizationRecovery,
        ``ManuscriptAudit.NodalSwapCoverEtale.cover_finite_etale,
        ``ManuscriptAudit.NodalSwapCoverEtale.cover_spec_surjective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
