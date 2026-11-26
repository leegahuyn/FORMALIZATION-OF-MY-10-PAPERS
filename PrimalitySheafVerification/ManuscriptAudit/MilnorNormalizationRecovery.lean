import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.TensorProduct.Prod
import PrimalitySheafVerification.ManuscriptAudit.MilnorNormalizationMap
import PrimalitySheafVerification.ManuscriptAudit.MilnorProjectivePatch

/-!
# Recovering normalization coordinates by scalar extension

On a block diagonal patch the extended first projection is the product
of the extended projections for the two blocks. Stabilizing with the
inverse transition matrix therefore reduces bijectivity to identity
gluing in twice the number of coordinates.
-/

namespace ManuscriptAudit.MilnorNormalizationRecovery

open Matrix MilnorCoordinatePatch MilnorNormalizationMap MilnorProjectivePatch
open scoped TensorProduct

universe u v

variable {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
variable [Algebra A B] [Algebra A C] [Algebra A D]
variable {n : Type v} [Fintype n]
variable (q : B →ₐ[A] D) (s : C →ₐ[A] D)

set_option backward.isDefEq.respectTransparency false in
/-- The two first-coordinate maps form the first-coordinate map of the block patch. -/
theorem normalizationMap_block (U W : Matrix n n D) :
    (LinearEquiv.sumArrowLequivProdArrow n n B B).toLinearMap.comp
      ((normalizationMap q s (fromBlocks U 0 0 W)).comp
        ((blockPatchEquiv q s U W).baseChange A B _ _).toLinearMap) =
      ((normalizationMap q s U).prodMap (normalizationMap q s W)).comp
        (TensorProduct.prodRight A B B (patch q s U) (patch q s W)).toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro b x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.baseChange_tmul,
    TensorProduct.prodRight_tmul, LinearMap.prodMap_apply, normalizationMap_tmul] <;> rfl

variable [DecidableEq n]

set_option backward.isDefEq.respectTransparency false in
/-- For a surjective reduction map, recovery over the normalization follows from
recovery for the identity transition in twice the number of coordinates. -/
theorem normalizationMap_bijective (hq : Function.Surjective q) (U : GL n D)
    (hIdentity : Function.Bijective
      (normalizationMap q s (1 : Matrix (n ⊕ n) (n ⊕ n) D))) :
    Function.Bijective (normalizationMap q s U.val) := by
  obtain ⟨V, hV⟩ := MilnorStabilizedMatrix.stabilized_lifts q.toRingHom hq U
  have hDouble : Function.Bijective (normalizationMap q s (fromBlocks U.val 0 0 U.inv)) :=
    normalizationMap_bijective_of_lift q s (MilnorStabilizedMatrix.stabilized U) V hV hIdentity
  let ePatch := (blockPatchEquiv q s U.val U.inv).baseChange A B _ _
  let eCoordinates := LinearEquiv.sumArrowLequivProdArrow n n B B
  let eTensor := TensorProduct.prodRight A B B (patch q s U.val) (patch q s U.inv)
  let f := (normalizationMap q s U.val).prodMap (normalizationMap q s U.inv)
  have h :
      f ∘ eTensor = eCoordinates ∘ (normalizationMap q s (fromBlocks U.val 0 0 U.inv)) ∘ ePatch :=
    funext fun x => (DFunLike.congr_fun (normalizationMap_block q s U.val U.inv) x).symm
  have hComp : Function.Bijective (f ∘ eTensor) := by
    rw [h]
    exact eCoordinates.bijective.comp (hDouble.comp ePatch.bijective)
  have hFun : (f : _ → _) = (f ∘ eTensor) ∘ eTensor.symm :=
    funext fun x => (congrArg f (eTensor.apply_symm_apply x)).symm
  have hProd : Function.Bijective f := by
    rw [hFun]
    exact hComp.comp eTensor.symm.bijective
  constructor
  · intro x y hxy
    have hPair : f (x, 0) = f (y, 0) := Prod.ext hxy rfl
    exact congrArg Prod.fst (hProd.injective hPair)
  · intro y
    obtain ⟨x, hx⟩ := hProd.surjective (y, 0)
    exact ⟨x.1, congrArg Prod.fst hx⟩

end ManuscriptAudit.MilnorNormalizationRecovery

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.MilnorNormalizationRecovery.normalizationMap_block,
      ``ManuscriptAudit.MilnorNormalizationRecovery.normalizationMap_bijective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
