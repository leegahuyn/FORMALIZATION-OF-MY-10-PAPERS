import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.TensorProduct.Quotient
import PrimalitySheafVerification.ManuscriptAudit.NodalAffineOrigin
import PrimalitySheafVerification.ManuscriptAudit.NodalMilnorCoefficients
import PrimalitySheafVerification.ManuscriptAudit.NodalNormalization

/-! The fiber of the native finite affine normalization at the conductor is
the spectrum of the two independent rational branches. -/

namespace ManuscriptAudit.NodalNormalizationFiber

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NodalConductor
open scoped TensorProduct

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (K : Type u) [Field K]

abbrev A := coordinates K
abbrev B := Polynomial K

attribute [local instance] NodalMilnorCoefficients.originAlgebra

def originIdeal : Ideal (A K) := RingHom.ker (algebraMap (A K) K)

/-- The conductor point's ideal extends to the principal ideal (t²−1). -/
theorem origin_ideal_map (h2 : (2 : K) ≠ 0) :
    (originIdeal K).map (algebraMap (A K) (B K)) = Ideal.span {x K} := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change a.val ∈ Ideal.span {x K}
    rw [Ideal.mem_span_singleton, x_dvd_iff_vanishes K h2]
    have h₁ : a.val.eval 1 = 0 := RingHom.mem_ker.mp ha
    have h₂ : a.val.eval 1 = a.val.eval (-1) :=
      (mem_equalBranchValues K a.val).mp (coordinates_le_equalBranchValues K a.property)
    exact ⟨h₁, h₂.symm.trans h₁⟩
  · apply Ideal.span_le.mpr
    intro a ha
    obtain rfl : a = x K := Set.mem_singleton_iff.mp ha
    let t : A K := NodalAffinePresentation.nodeX K
    have ht : t ∈ originIdeal K := RingHom.mem_ker.mpr (NodalAffineOrigin.originAlgebra_x K)
    exact Ideal.mem_map_of_mem (algebraMap (A K) (B K)) ht

private def quotientOrigin :
    (A K ⧸ originIdeal K) ≃ₐ[A K] K :=
  Ideal.quotientKerAlgEquivOfSurjective
    (f := Algebra.ofId (A K) K) (fun c =>
      ⟨algebraMap K (A K) c, (NodalAffineOrigin.originAlgebra K).commutes c⟩)

abbrev fiberRing := K ⊗[A K] B K

/-- The scheme-theoretic fiber ring of the affine normalization is K × K. -/
def fiberRingEquiv (h2 : (2 : K) ≠ 0) : fiberRing K ≃+* K × K :=
  (Algebra.TensorProduct.congr (quotientOrigin K).symm (AlgEquiv.refl : B K ≃ₐ[A K] B K)).toRingEquiv
    |>.trans (Algebra.TensorProduct.quotIdealMapEquivQuotTensor (B K) (originIdeal K)).symm.toRingEquiv
    |>.trans (Ideal.quotEquivOfEq
      ((origin_ideal_map K h2).trans (NodalConductorSquare.branches_ker K h2).symm))
    |>.trans ((NodalConductorSquare.branches K).hom.quotientKerEquivOfSurjective
      (NodalConductorSquare.branches_surjective K h2))

abbrev affineLine : Scheme.{u} := Spec (CommRingCat.of (B K))
abbrev affineNode : Scheme.{u} := Spec (CommRingCat.of (A K))

def affineNormalization : affineLine K ⟶ affineNode K :=
  Spec.map (CommRingCat.ofHom (algebraMap (A K) (B K)))

private def fiberFirst : Spec (CommRingCat.of (fiberRing K)) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom
    ((Algebra.TensorProduct.includeLeft : K →ₐ[A K] fiberRing K).toRingHom))

private def fiberSecond : Spec (CommRingCat.of (fiberRing K)) ⟶ affineLine K :=
  Spec.map (CommRingCat.ofHom
    ((Algebra.TensorProduct.includeRight : B K →ₐ[A K] fiberRing K).toRingHom))

private theorem tensor_isPullback :
    IsPullback (fiberFirst K) (fiberSecond K) (NodalAffineOrigin.originMap K) (affineNormalization K) := by
  change IsPullback (fiberFirst K) (fiberSecond K)
    (Spec.map (CommRingCat.ofHom (algebraMap (A K) K))) (affineNormalization K)
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    ⟨⟨(CommRingCat.pushoutCocone (A K) K (B K)).condition⟩,
      ⟨CommRingCat.pushoutCoconeIsColimit (A K) K (B K)⟩⟩

/-- The actual fiber at the rational singular point is the two-point split scheme. -/
def conductorFiberIso (h2 : (2 : K) ≠ 0) :
    pullback (NodalAffineOrigin.originMap K) (affineNormalization K) ≅
      Spec (CommRingCat.of (K × K)) :=
  (tensor_isPullback K).isoPullback.symm ≪≫
    Scheme.Spec.mapIso (fiberRingEquiv K h2).symm.toCommRingCatIso.op

end
end ManuscriptAudit.NodalNormalizationFiber

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalNormalizationFiber.origin_ideal_map,
      ``ManuscriptAudit.NodalNormalizationFiber.fiberRingEquiv,
      ``ManuscriptAudit.NodalNormalizationFiber.conductorFiberIso] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
