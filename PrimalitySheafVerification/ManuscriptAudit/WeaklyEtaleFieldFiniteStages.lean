import Lean.Util.CollectAxioms
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.Etale.Field
import PrimalitySheafVerification.ManuscriptAudit.WeaklyEtaleClosedFieldEvaluation

/-! Every finitely generated subalgebra of an actual weakly étale
algebra over a field is finite étale, including imperfect base fields. -/

namespace ManuscriptAudit.WeaklyEtaleFieldFiniteStages

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ProetaleAffineTensor (structureMap specMap leftInclusion specTensor_isPullback)
open scoped TensorProduct

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (K B : Type u) [Field K] [CommRing B] [Algebra K B]
  [WeaklyEtale (structureMap K B)]

private abbrev E := AlgebraicClosure K
private abbrev T := E K ⊗[K] B

private theorem geometricFiber_weaklyEtale :
    WeaklyEtale (structureMap (E K) (T K B)) := by
  change WeaklyEtale (specMap K (leftInclusion K (E K) B))
  exact MorphismProperty.of_isPullback (P := @WeaklyEtale)
    (specTensor_isPullback K (E K) B).flip (inferInstanceAs (WeaklyEtale (structureMap K B)))

theorem geometricFiber_reduced : IsReduced (T K B) := by
  letI : WeaklyEtale (structureMap (E K) (T K B)) := geometricFiber_weaklyEtale K B
  exact WeaklyEtaleAffineLineReducedFibres.reduced_over_algebraicallyClosed
    (structureMap (E K) (T K B))

/-- Every element is integral over the ground field. -/
theorem isIntegral (b : B) : IsIntegral K b := by
  let i : B →ₐ[K] T K B := Algebra.TensorProduct.includeRight
  have hi : Function.Injective i := Algebra.TensorProduct.includeRight_injective
    (FaithfulSMul.algebraMap_injective K (E K))
  letI : WeaklyEtale (structureMap (E K) (T K B)) := geometricFiber_weaklyEtale K B
  have hb : IsIntegral (E K) (i b) :=
    WeaklyEtaleClosedFieldEvaluation.isIntegral (E K) (T K B) (i b)
  have hb' : IsAlgebraic K (i b) := IsIntegral.trans_isAlgebraic K hb
  exact (isIntegral_algHom_iff i hi).mp hb'.isIntegral

private theorem finite_reduced_over_closed (k D : Type u) [Field k] [IsAlgClosed k]
    [CommRing D] [Algebra k D] [Module.Finite k D] [IsReduced D] : Algebra.Etale k D := by
  letI : IsArtinianRing D := isArtinian_of_tower k inferInstance
  let Q (m : MaximalSpectrum D) := D ⧸ m.asIdeal
  letI (m : MaximalSpectrum D) : Field (Q m) := Ideal.Quotient.field m.asIdeal
  letI (m : MaximalSpectrum D) : Module.Finite k (Q m) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ k m.asIdeal).toLinearMap
      Ideal.Quotient.mk_surjective
  let e (m : MaximalSpectrum D) : k ≃ₐ[k] Q m :=
    AlgEquiv.ofBijective (Algebra.ofId k (Q m)) IsAlgClosed.algebraMap_bijective_of_isIntegral
  let eD := ((IsArtinianRing.equivPi D).restrictScalars k).trans
    (AlgEquiv.piCongrRight fun m ↦ (e m).symm)
  exact (Algebra.Etale.iff_exists_algEquiv_prod k D).mpr
    ⟨MaximalSpectrum D, inferInstance, fun _ ↦ k, fun _ ↦ inferInstance, fun _ ↦ inferInstance,
      eD, fun _ ↦ ⟨inferInstance, inferInstance⟩⟩

set_option maxHeartbeats 2000000 in
/-- Each literal finite generated subalgebra is finite étale over the base. -/
theorem adjoin_finite_etale (s : Set B) (hs : s.Finite) :
    Module.Finite K (Algebra.adjoin K s) ∧ Algebra.Etale K (Algebra.adjoin K s) := by
  let D := Algebra.adjoin K s
  letI : Module.Finite K D :=
    Algebra.finite_adjoin_of_finite_of_isIntegral hs (fun b _ ↦ isIntegral K B b)
  let S := E K ⊗[K] D
  let j : D →ₐ[K] B := D.val
  let f : S →ₐ[K] T K B := Algebra.TensorProduct.map (AlgHom.id K (E K)) j
  have hf : Function.Injective f := by
    have h : f.toLinearMap = j.toLinearMap.lTensor (E K) := by
      apply TensorProduct.ext'
      intro a b
      rfl
    change Function.Injective f.toLinearMap
    rw [h]
    exact Module.Flat.lTensor_preserves_injective_linearMap j.toLinearMap Subtype.val_injective
  letI : IsReduced (T K B) := geometricFiber_reduced K B
  letI : IsReduced S := isReduced_of_injective f hf
  letI : Algebra.Etale (E K) S := finite_reduced_over_closed (E K) S
  exact ⟨inferInstanceAs (Module.Finite K D),
    Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat (E K)⟩

end
end ManuscriptAudit.WeaklyEtaleFieldFiniteStages

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeaklyEtaleFieldFiniteStages.geometricFiber_reduced,
      ``ManuscriptAudit.WeaklyEtaleFieldFiniteStages.isIntegral,
      ``ManuscriptAudit.WeaklyEtaleFieldFiniteStages.adjoin_finite_etale] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
