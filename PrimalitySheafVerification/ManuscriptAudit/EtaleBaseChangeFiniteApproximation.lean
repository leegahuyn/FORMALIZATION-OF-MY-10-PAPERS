import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.WeaklyEtaleAffineLineGlobalStage
import PrimalitySheafVerification.ManuscriptAudit.AffineStageTensorExtensionMaps

/-! Absolute affine étale approximations pass to an étale base,
in particular to every actual principal open of the affine line. -/

namespace ManuscriptAudit.EtaleBaseChangeFiniteApproximation

open AlgebraicGeometry CategoryTheory
open ProetaleAffineTensor (structureMap specMap)
open AffineEtaleStageColimit (FiniteTupleApproximation)
open AffineStageTensorExtensionMaps (extend extend_includeRight)
open scoped TensorProduct

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

/-- All weakly étale affine charts of the specified base have finite tuple approximations. -/
abbrev HasWeaklyEtaleApproximations (A : Type u) [CommRing A] : Prop :=
  ∀ (B : Type u) [CommRing B] [Algebra A B] [WeaklyEtale (structureMap A B)],
    FiniteTupleApproximation A B

variable {A S : Type u} [CommRing A] [CommRing S] [Algebra A S] [Algebra.Etale A S]

set_option maxHeartbeats 3900000 in
/-- Étale base change of an actual weakly étale affine approximation. -/
theorem of_etale (h : HasWeaklyEtaleApproximations A) :
    HasWeaklyEtaleApproximations S := by
  intro B hB hSB hWB ι hι z
  letI : Algebra A B := Algebra.compHom B (algebraMap A S)
  letI : IsScalarTower A S B := IsScalarTower.of_algebraMap_eq' rfl
  letI : Etale (structureMap A S) :=
    (HasRingHomProperty.Spec_iff (P := @Etale) (φ := CommRingCat.ofHom (algebraMap A S))).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)
  have he : structureMap S B ≫ structureMap A S = structureMap A B := by
    change specMap A (IsScalarTower.toAlgHom A S B) ≫ structureMap A S = _
    exact ProetaleAffineTensor.specMap_structureMap A (IsScalarTower.toAlgHom A S B)
  letI : WeaklyEtale (structureMap A B) :=
    he ▸ inferInstanceAs (WeaklyEtale (structureMap S B ≫ structureMap A S))
  obtain ⟨C, hC, hAC, hE, f, hf⟩ := h B z
  letI : CommRing C := hC
  letI : Algebra A C := hAC
  letI : Algebra.Etale A C := hE
  let D := S ⊗[A] C
  let g : D →ₐ[S] B := extend f
  refine ⟨D, inferInstance, inferInstance, inferInstance, g, ?_⟩
  intro i
  obtain ⟨a, ha⟩ := hf i
  refine ⟨Algebra.TensorProduct.includeRight a, ?_⟩
  exact (DFunLike.congr_fun (extend_includeRight (B := S) f) a).trans ha

/-- The finite-stage theorem applies over the affine line itself. -/
theorem affineLine (K : Type u) [Field K] [IsAlgClosed K] :
    HasWeaklyEtaleApproximations (Polynomial K) := by
  intro B hB hAB hWB
  exact WeaklyEtaleAffineLineGlobalStage.exists_global_stage K B

/-- The actual principal affine open inherits the full weakly étale approximation theorem. -/
theorem principalOpen (K : Type u) [Field K] [IsAlgClosed K] (g : Polynomial K) :
    HasWeaklyEtaleApproximations (Localization.Away g) :=
  of_etale (A := Polynomial K) (S := Localization.Away g) (affineLine K)

end
end ManuscriptAudit.EtaleBaseChangeFiniteApproximation

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleBaseChangeFiniteApproximation.of_etale,
      ``ManuscriptAudit.EtaleBaseChangeFiniteApproximation.principalOpen] do
    let ax ← collectAxioms name
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
