import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.TensorProduct.Prod
import PrimalitySheafVerification.ManuscriptAudit.InvolutionTensorBaseChange

/-!
# Scalar extension of a certified two-copy comparison

The canonical formula alone identifies the comparison after arbitrary
scalar extension, by the native tensor distribution equivalences.
-/

namespace ManuscriptAudit.CertifiedTorsorBaseChange

open InvolutionTensorComparison InvolutionTensorBaseChange
open scoped TensorProduct

noncomputable section

variable (A E B : Type*) [CommRing A] [CommRing E] [CommRing B] [Algebra A E] [Algebra A B]

private abbrev D := B ⊗[A] E

local instance productTower (P Q : Type*) [CommRing P] [CommRing Q] [Algebra P Q] :
    IsScalarTower P Q (Q × Q) where
  smul_assoc a b z := Prod.ext (smul_assoc a b z.1) (smul_assoc a b z.2)

/-- Transport an actual canonical equivalence to every base algebra. -/
def liftCertified (σ : E ≃ₐ[A] E) (cert : CertifiedComparison A E σ) :
    CertifiedComparison B (D A E B) (baseSwap A E B σ) := by
  let assoc := TensorProduct.AlgebraTensorModule.distribBaseChange A B E E
  let lift := (cert.equiv.toLinearEquiv.restrictScalars A).baseChange A B (E ⊗[A] E) (E × E)
  let split := TensorProduct.prodRight A B B E E
  let cmp := comparison B (D A E B) (baseSwap A E B σ)
  let cmpLinear : D A E B ⊗[B] D A E B →ₗ[B] D A E B × D A E B :=
    cmp.toLinearMap.restrictScalars B
  have hLift (b : B) (z : E ⊗[A] E) : lift (b ⊗ₜ[A] z) = b ⊗ₜ[A] cert.equiv z := rfl
  have hMap : cmpLinear.comp assoc.toLinearMap = split.toLinearMap.comp lift.toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro b z
    change cmp (assoc (b ⊗ₜ[A] z)) = split (lift (b ⊗ₜ[A] z))
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      have hc : cert.equiv (x ⊗ₜ[A] y) = (x * y, x * σ y) := cert.on_tmul x y
      rw [hLift, hc]
      simp only [assoc, TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
        cmp, comparison_tmul, baseSwap_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        split, TensorProduct.prodRight_tmul]
    | add x y hx hy =>
      simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hx hy
  have hFun : ⇑cmp = split ∘ lift ∘ assoc.symm := by
    funext z
    have h := DFunLike.congr_fun hMap (assoc.symm z)
    change cmp (assoc (assoc.symm z)) = split (lift (assoc.symm z)) at h
    rw [assoc.apply_symm_apply] at h
    exact h
  have hBij : Function.Bijective cmp := by
    rw [hFun]
    exact split.bijective.comp (lift.bijective.comp assoc.symm.bijective)
  exact ⟨AlgEquiv.ofBijective cmp hBij, comparison_tmul B (D A E B) (baseSwap A E B σ)⟩

end

end ManuscriptAudit.CertifiedTorsorBaseChange

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CertifiedTorsorBaseChange.liftCertified
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
