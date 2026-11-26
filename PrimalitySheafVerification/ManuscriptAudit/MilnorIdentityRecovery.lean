import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.TensorProduct.Pi
import PrimalitySheafVerification.ManuscriptAudit.MilnorIdentityGluing
import PrimalitySheafVerification.ManuscriptAudit.MilnorNormalizationRecovery

/-!
# Normalization recovery for identity transition

For identity gluing, every coordinate comes from a compatible scalar
pair. When those pairs are exactly the coefficient ring, scalar
extension of the first projection recovers all normalization coordinates.
-/

namespace ManuscriptAudit.MilnorIdentityRecovery

open Matrix MilnorCoordinatePatch MilnorIdentityGluing MilnorNormalizationMap
open scoped TensorProduct

noncomputable section

universe u v

variable {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
variable [Algebra A B] [Algebra A C] [Algebra A D]
variable {n : Type v} [Fintype n] [DecidableEq n]
variable (q : B →ₐ[A] D) (s : C →ₐ[A] D)

private theorem patch_eq_identity :
    patch q s (1 : Matrix n n D) = identityPatch q s n := by
  apply Submodule.ext
  intro x
  rw [mem_patch_one_iff]
  change (q ∘ x.1 = s ∘ x.2) ↔ ∀ i, q (x.1 i) = s (x.2 i)
  exact ⟨fun h i => congrFun h i, fun h => funext h⟩

private def identityCoordinates (hPair : Function.Bijective (pairMap q s)) :
    (n → A) ≃ₗ[A] patch q s (1 : Matrix n n D) :=
  (identityPatchEquiv q s n hPair).trans (LinearEquiv.ofEq _ _ (patch_eq_identity q s).symm)

private theorem identityCoordinates_fst (hPair : Function.Bijective (pairMap q s)) (x : n → A) :
    (identityCoordinates q s hPair x).val.1 = algebraMap A B ∘ x :=
  rfl

variable (A B n) in
private def freeCoordinatesBaseChange : B ⊗[A] (n → A) ≃ₗ[B] (n → B) :=
  (TensorProduct.piRight A B B (fun _ : n => A)).trans
    (LinearEquiv.piCongrRight fun _ : n => TensorProduct.AlgebraTensorModule.rid A B B)

private theorem freeCoordinatesBaseChange_tmul (b : B) (x : n → A) :
    freeCoordinatesBaseChange A B n (b ⊗ₜ[A] x) = b • (algebraMap A B ∘ x) := by
  funext i
  simp only [freeCoordinatesBaseChange, LinearEquiv.trans_apply, TensorProduct.piRight_apply,
    TensorProduct.piRightHom_tmul, LinearEquiv.piCongrRight_apply,
    TensorProduct.AlgebraTensorModule.rid_tmul, Function.comp_apply, Pi.smul_apply]
  change x i • b = b * algebraMap A B (x i)
  rw [Algebra.smul_def, mul_comm]

set_option backward.isDefEq.respectTransparency false in
/-- The first projection of an identity patch gives a bijection after scalar extension. -/
theorem normalizationMap_bijective_identity (hPair : Function.Bijective (pairMap q s)) :
    Function.Bijective (normalizationMap q s (1 : Matrix n n D)) := by
  let e : (B ⊗[A] (n → A)) ≃ₗ[B] B ⊗[A] patch q s (1 : Matrix n n D) :=
    (identityCoordinates (n := n) q s hPair).baseChange A B (n → A)
      (patch q s (1 : Matrix n n D))
  let eFree := freeCoordinatesBaseChange A B n
  have h : (normalizationMap q s (1 : Matrix n n D)).comp e.toLinearMap =
      eFree.toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro b x
    change b • (identityCoordinates (n := n) q s hPair x).val.1 =
      freeCoordinatesBaseChange A B n (b ⊗ₜ[A] x)
    rw [identityCoordinates_fst, freeCoordinatesBaseChange_tmul]
  have hf : ⇑(normalizationMap q s (1 : Matrix n n D)) = eFree ∘ e.symm := by
    funext x
    have hx := DFunLike.congr_fun h (e.symm x)
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
      Function.comp_apply] using hx
  rw [hf]
  exact eFree.bijective.comp e.symm.bijective

/-- A coefficient pullback recovers the normalization for every invertible transition matrix. -/
theorem normalizationMap_bijective (hq : Function.Surjective q)
    (hPair : Function.Bijective (pairMap q s)) (U : GL n D) :
    Function.Bijective (normalizationMap q s U.val) :=
  MilnorNormalizationRecovery.normalizationMap_bijective q s hq U
    (normalizationMap_bijective_identity (n := n ⊕ n) q s hPair)

end

end ManuscriptAudit.MilnorIdentityRecovery

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.MilnorIdentityRecovery.normalizationMap_bijective_identity,
      ``ManuscriptAudit.MilnorIdentityRecovery.normalizationMap_bijective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
