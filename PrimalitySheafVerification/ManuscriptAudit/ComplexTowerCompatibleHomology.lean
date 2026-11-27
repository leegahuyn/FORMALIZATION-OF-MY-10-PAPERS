import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import PrimalitySheafVerification.ManuscriptAudit.ExactLimitComplexHomology
import PrimalitySheafVerification.ManuscriptAudit.ComplexTowerFiberKernel
import PrimalitySheafVerification.ManuscriptAudit.AbProductDifference

/-! Mapping fibers of countable Ab-complex towers and their compatible homology classes. -/

namespace ManuscriptAudit.ComplexTowerCompatibleHomology

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open ComplexTowerDifference (difference mappingFiber)
open CyclicPowerInverseLimit (compatibleTuples)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{0}
private abbrev Ch := CochainComplex A ℤ

variable (K : ℕ → Ch) (transition : ∀ r, K (r + 1) ⟶ K r)

private abbrev H (n : ℤ) := homologyFunctor A (ComplexShape.up ℤ) n

/-- The canonical product comparison is an isomorphism, by exactness of products in Ab. -/
def productHomologyIso (n : ℤ) :
    (∏ᶜ K).homology n ≅ ∏ᶜ (fun r ↦ (K r).homology n) := by
  letI : PreservesLimit (Discrete.functor K) (H n) :=
    ExactLimitComplexHomology.preservesLimit (Discrete.functor K) n
  exact PreservesProduct.iso (H n) K

private theorem difference_comm (n : ℤ) :
    homologyMap (difference K transition) n ≫ (productHomologyIso K n).hom =
      (productHomologyIso K n).hom ≫
        difference (fun r ↦ (K r).homology n) (fun r ↦ homologyMap (transition r) n) :=
  ComplexTowerDifference.homology_difference K transition n

/-- Onto finite-level transitions make the native product difference epic on homology. -/
theorem homology_difference_epi (n : ℤ)
    (onto : ∀ r, Function.Surjective (homologyMap (transition r) n :
      (K (r + 1)).homology n → (K r).homology n)) :
    Epi (homologyMap (difference K transition) n) := by
  let d := homologyMap (difference K transition) n
  let e := productHomologyIso K n
  let d' := difference (fun r ↦ (K r).homology n) (fun r ↦ homologyMap (transition r) n)
  letI : Epi d' := AbProductDifference.difference_epi _ _ onto
  have h : Epi (e.hom ≫ d') := inferInstance
  have hw : d ≫ e.hom = e.hom ≫ d' := difference_comm K transition n
  rw [← hw] at h
  letI := h
  exact epi_of_epi d e.hom

variable [HasDerivedCategory A]

/-- If the transitions are onto in the preceding degree, the homology of the
actual complex mapping fiber is the group of compatible classes in the current degree. -/
def fiberHomologyEquiv (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁)
    (onto : ∀ r, Function.Surjective (homologyMap (transition r) n₀ :
      (K (r + 1)).homology n₀ → (K r).homology n₀)) :
    (mappingFiber K transition).homology n₁ ≃+
      compatibleTuples (fun r ↦ (K r).homology n₁)
        (fun r ↦ (homologyMap (transition r) n₁).hom) := by
  letI := homology_difference_epi K transition n₀ onto
  let a := ComplexTowerFiberKernel.homologyKernelIso K transition n₀ n₁ h
  let e := productHomologyIso K n₁
  let d' := difference (fun r ↦ (K r).homology n₁) (fun r ↦ homologyMap (transition r) n₁)
  let b := kernel.mapIso (homologyMap (difference K transition) n₁) d' e e
    (difference_comm K transition n₁)
  exact (a ≪≫ b).addCommGroupIsoToAddEquiv.trans (AbProductDifference.kernelEquiv _ _)

end
end ManuscriptAudit.ComplexTowerCompatibleHomology

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ComplexTowerCompatibleHomology.productHomologyIso,
      ``ManuscriptAudit.ComplexTowerCompatibleHomology.homology_difference_epi,
      ``ManuscriptAudit.ComplexTowerCompatibleHomology.fiberHomologyEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
