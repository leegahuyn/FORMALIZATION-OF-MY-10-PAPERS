import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalProetaleConductorSequence
import PrimalitySheafVerification.ManuscriptAudit.ProetaleContinuousCoefficientNaturality
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicResidueKernelMap
import PrimalitySheafVerification.ManuscriptAudit.ProetaleInverseImage
import PrimalitySheafVerification.ManuscriptAudit.ProetaleCountableProductEpi
import PrimalitySheafVerification.ManuscriptAudit.ShortExactKernelEpi
import PrimalitySheafVerification.ManuscriptAudit.ShortComplexTowerProduct

/-! The actual proper nodal conductor sequence is short exact also for
continuous integral adic coefficients. -/

namespace ManuscriptAudit.NodalNativeAdicConductorSequence

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NodalProjectiveClosure (projectiveNode)
open NodalProjectiveNormalization (normalizationMap normalizationMap_integral normalizedNode)
open NodalNormalizedMapSurjectivity (properNormalization_surjective)
open NodalSmoothRationalBoundary (projectiveOrigin)
open NodalProetaleConductorBinary (plus minus plus_over minus_over)
open NodalProetaleConductorSequence (sequence)
open ProetaleBaseChange (directImage)
open ProetaleCoefficientUniverseLift (lift)
open ProetaleResidueSheaves (residueReduction residueReduction_comp)
open ProetaleAdicResidueKernelMap (inclusion_comp inclusionIsKernel)
open ShortComplexTowerProduct (consecutive toProduct)
open AbelianCountableProductShortExact (product product_shortExact)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] (h2 : (2 : K) ≠ 0) (ℓ : ℕ) [Fact ℓ.Prime]

local instance residueTopology (d : ℕ) : TopologicalSpace (ZMod d) := ⊥
local instance residueDiscrete (d : ℕ) : DiscreteTopology (ZMod d) := ⟨rfl⟩

private abbrev X := projectiveNode K
private abbrev N := normalizedNode K
private abbrev O := Spec (CommRingCat.of K)
private abbrev A := AddCommGrpCat.{1}

private instance image_rightAdjoint {Y Z : Scheme.{0}} (i : Y ⟶ Z) :
    (directImage i A).IsRightAdjoint := (ProetaleInverseImage.adjunction i).isRightAdjoint

private instance image_additive {Y Z : Scheme.{0}} (i : Y ⟶ Z) :
    (directImage i A).Additive := (directImage i A).additive_of_preserves_binary_products

private abbrev qN := lift (N K) ⋙ directImage (normalizationMap K) A
private abbrev qO := lift (O K) ⋙ directImage (projectiveOrigin K) A

private abbrev R (n : ℕ) := sequence K h2 (ZMod (ℓ ^ n))

private abbrev t (n : ℕ) : R K h2 ℓ (n+1) ⟶ R K h2 ℓ n :=
  ProetaleContinuousCoefficientNaturality.sequenceMap
    (PadicResidueSystems.reduction ℓ (Nat.le_succ n)).toAddMonoidHom
    continuous_of_discreteTopology (normalizationMap K) (projectiveOrigin K)
    (plus K h2) (minus K h2) (plus_over K h2) (minus_over K h2)

private abbrev r (n : ℕ) : sequence K h2 ℤ_[ℓ] ⟶ R K h2 ℓ n :=
  ProetaleContinuousCoefficientNaturality.sequenceMap
    (PadicInt.toZModPow n).toAddMonoidHom
    (PadicResidueHomeomorphism.reduction_continuous ℓ n)
    (normalizationMap K) (projectiveOrigin K)
    (plus K h2) (minus K h2) (plus_over K h2) (minus_over K h2)

set_option maxHeartbeats 1700000 in
/-- Exactness holds integrally for the genuine topological coefficient sheaf;
the connecting comparison uses the exact product of all finite rows. -/
theorem shortExact : (sequence K h2 ℤ_[ℓ]).ShortExact := by
  let P := product (R K h2 ℓ)
  let D := consecutive (R K h2 ℓ) (t K h2 ℓ)
  let j := toProduct (R K h2 ℓ) (r K h2 ℓ)
  have h₂ : j.τ₂ ≫ D.τ₂ = 0 := inclusion_comp (N K) ℓ (qN K)
  have h₃ : j.τ₃ ≫ D.τ₃ = 0 := inclusion_comp (O K) ℓ (qO K)
  have k₂ : IsLimit (KernelFork.ofι j.τ₂ h₂) := inclusionIsKernel (N K) ℓ (qN K)
  have k₃ : IsLimit (KernelFork.ofι j.τ₃ h₃) := inclusionIsKernel (O K) ℓ (qO K)
  have hR (n : ℕ) : (R K h2 ℓ n).ShortExact :=
    NodalProetaleConductorSequence.sequence_shortExact K h2 (ZMod (ℓ ^ n))
  have hP : Epi P.g :=
    ProetaleCountableProductEpi.product_epi (fun n ↦ (R K h2 ℓ n).g)
      (fun n ↦ (hR n).epi_g)
  letI : Epi P.g := hP
  letI : Epi D.τ₁ := ProetaleAdicResidueKernelMap.native_difference_epi (X K) ℓ
  letI : Epi (ProetaleTwoBranchKernel.difference (normalizationMap K) (projectiveOrigin K)
      (plus K h2) (minus K h2) (plus_over K h2) (minus_over K h2) ℤ_[ℓ]) :=
    (show Epi (sequence K h2 ℤ_[ℓ]).g from
      ShortExactKernelEpi.epi_right D j (product_shortExact (R K h2 ℓ) hR hP).exact k₂ k₃)
  letI := normalizationMap_integral K
  letI := properNormalization_surjective K h2
  exact ProetaleTwoBranchKernel.sequence_shortExact _ _ _ _ _ _ _
    (NodalProperNormalizationFibers.branchFibers K h2)

end
end ManuscriptAudit.NodalNativeAdicConductorSequence

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NodalNativeAdicConductorSequence.shortExact
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{name} depends on unexpected axioms {ax}"
  logInfo m!"{name} uses {ax}"
