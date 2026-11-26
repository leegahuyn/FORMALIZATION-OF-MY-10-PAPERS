import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Finite
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

private theorem quotientEq_mk {I J : Ideal (B K)} (h : I = J) (b : B K) :
    Ideal.quotEquivOfEq h (Ideal.Quotient.mk I b) = Ideal.Quotient.mk J b := by
  subst J
  rfl

/-- Over the conductor, the inclusion of the polynomial line is actual
evaluation at the two ordered rational branch values. -/
theorem fiberRingEquiv_polynomial (h2 : (2 : K) ≠ 0) (b : B K) :
    fiberRingEquiv K h2 (1 ⊗ₜ[A K] b) = (b.eval 1, b.eval (-1)) := by
  let e := quotientOrigin K
  let a := Algebra.TensorProduct.quotIdealMapEquivQuotTensor (B K) (originIdeal K)
  let i := (origin_ideal_map K h2).trans (NodalConductorSquare.branches_ker K h2).symm
  let q := (NodalConductorSquare.branches K).hom.quotientKerEquivOfSurjective
    (NodalConductorSquare.branches_surjective K h2)
  change q (Ideal.quotEquivOfEq i (a.symm
    (Algebra.TensorProduct.congr e.symm (AlgEquiv.refl : B K ≃ₐ[A K] B K)
      (1 ⊗ₜ[A K] b)))) = _
  rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, map_one]
  change q (Ideal.quotEquivOfEq i (a.symm (1 ⊗ₜ[A K] b))) = _
  have h : a.symm (1 ⊗ₜ[A K] b) = Ideal.Quotient.mk _ b := by
    apply a.injective
    rw [AlgEquiv.apply_symm_apply]
    exact (Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk _ _ _).symm
  rw [h, quotientEq_mk]
  exact RingHom.quotientKerEquivOfSurjective_apply_mk _ b

abbrev affineLine : Scheme.{u} := Spec (CommRingCat.of (B K))
abbrev affineNode : Scheme.{u} := Spec (CommRingCat.of (A K))

def affineNormalization : affineLine K ⟶ affineNode K :=
  Spec.map (CommRingCat.ofHom (algebraMap (A K) (B K)))

/-- The actual affine nodal normalization is finite. -/
theorem affineNormalization_finite (h2 : (2 : K) ≠ 0) : IsFinite (affineNormalization K) := by
  letI : Module.Finite (A K) (B K) := NodalNormalization.normalization_finite K h2
  apply (IsFinite.SpecMap_iff _).mpr
  exact RingHom.finite_algebraMap.mpr inferInstance

/-- The actual affine nodal normalization is surjective on the native scheme. -/
theorem affineNormalization_surjective (h2 : (2 : K) ≠ 0) :
    Function.Surjective (affineNormalization K) := by
  letI : Module.Finite (A K) (B K) := NodalNormalization.normalization_finite K h2
  letI : Algebra.IsIntegral (A K) (B K) := Algebra.IsIntegral.of_finite _ _
  exact Algebra.IsIntegral.comap_surjective (A K) (B K)

/-- The native normalization is a quotient map on points. -/
theorem affineNormalization_quotient (h2 : (2 : K) ≠ 0) :
    Topology.IsQuotientMap (affineNormalization K) := by
  letI : IsFinite (affineNormalization K) := affineNormalization_finite K h2
  exact (affineNormalization K).isClosedMap.isQuotientMap
    (affineNormalization K).continuous (affineNormalization_surjective K h2)

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

/-- Under the scheme fiber identification, its second projection is
the morphism defined by evaluation on the two ordered branches. -/
theorem conductorFiberIso_second (h2 : (2 : K) ≠ 0) :
    (conductorFiberIso K h2).hom ≫ Spec.map (NodalConductorSquare.branches K) =
      pullback.snd (NodalAffineOrigin.originMap K) (affineNormalization K) := by
  apply (cancel_epi (tensor_isPullback K).isoPullback.hom).mp
  simp only [conductorFiberIso, Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]
  rw [(tensor_isPullback K).isoPullback_hom_snd]
  change Spec.map (CommRingCat.ofHom (fiberRingEquiv K h2).symm.toRingHom) ≫
    Spec.map (NodalConductorSquare.branches K) = fiberSecond K
  rw [← Spec.map_comp]
  unfold fiberSecond
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro f
  change (fiberRingEquiv K h2).symm (f.eval 1, f.eval (-1)) = (1 ⊗ₜ[A K] f)
  apply (fiberRingEquiv K h2).injective
  rw [RingEquiv.apply_symm_apply, fiberRingEquiv_polynomial]

end
end ManuscriptAudit.NodalNormalizationFiber

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalNormalizationFiber.origin_ideal_map,
      ``ManuscriptAudit.NodalNormalizationFiber.fiberRingEquiv,
      ``ManuscriptAudit.NodalNormalizationFiber.fiberRingEquiv_polynomial,
      ``ManuscriptAudit.NodalNormalizationFiber.affineNormalization_finite,
      ``ManuscriptAudit.NodalNormalizationFiber.affineNormalization_quotient,
      ``ManuscriptAudit.NodalNormalizationFiber.conductorFiberIso,
      ``ManuscriptAudit.NodalNormalizationFiber.conductorFiberIso_second] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
