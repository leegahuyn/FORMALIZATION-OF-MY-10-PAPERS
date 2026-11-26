import Lean.Util.CollectAxioms
import Mathlib.Algebra.Module.Projective
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import PrimalitySheafVerification.ManuscriptAudit.MilnorCoordinatePatch
import PrimalitySheafVerification.ManuscriptAudit.MilnorStabilizedMatrix

/-!
# Finite projectivity from stabilized coordinate patching

The product of two fixed-coordinate patches is the patch with block
diagonal transition matrix. The patch with inverse transition is
therefore a complement: stabilization lifts to an invertible matrix,
and the identity patch supplies a finite free module.
-/

namespace ManuscriptAudit.MilnorProjectivePatch

open Matrix MilnorCoordinatePatch

universe u v

variable {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
variable [Algebra A B] [Algebra A C] [Algebra A D]
variable {n : Type v} [Fintype n]
variable (q : B →ₐ[A] D) (s : C →ₐ[A] D)

private def submoduleProdEquiv {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    [Module A M] [Module A N] (P : Submodule A M) (Q : Submodule A N) :
    P × Q ≃ₗ[A] P.prod Q where
  toFun x := ⟨(x.1.val, x.2.val), ⟨x.1.property, x.2.property⟩⟩
  invFun x := (⟨x.val.1, x.property.1⟩, ⟨x.val.2, x.property.2⟩)
  left_inv x := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl
  right_inv x := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

variable (A B C n) in
private def mergeCoordinates :
    (((n → B) × (n → C)) × ((n → B) × (n → C))) ≃ₗ[A]
      (((n ⊕ n) → B) × ((n ⊕ n) → C)) :=
  (LinearEquiv.prodProdProdComm A (n → B) (n → C) (n → B) (n → C)).trans
    ((LinearEquiv.sumArrowLequivProdArrow n n A B).symm.prodCongr
      (LinearEquiv.sumArrowLequivProdArrow n n A C).symm)

set_option backward.isDefEq.respectTransparency false in
/-- Taking the product of two coordinate patches gives the block diagonal patch. -/
def blockPatchEquiv (U W : Matrix n n D) :
    (patch q s U × patch q s W) ≃ₗ[A] patch q s (fromBlocks U 0 0 W) := by
  let e := mergeCoordinates A B C n
  refine (submoduleProdEquiv (patch q s U) (patch q s W)).trans (e.ofSubmodules _ _ ?_)
  apply Submodule.ext
  intro x
  simp only [Submodule.mem_map_equiv, Submodule.mem_prod, mem_patch_iff]
  change ((q ∘ (x.1 ∘ Sum.inl) = U *ᵥ (s ∘ (x.2 ∘ Sum.inl))) ∧
    (q ∘ (x.1 ∘ Sum.inr) = W *ᵥ (s ∘ (x.2 ∘ Sum.inr)))) ↔
      q ∘ x.1 = fromBlocks U 0 0 W *ᵥ (s ∘ x.2)
  simp only [fromBlocks_mulVec, zero_mulVec, add_zero, zero_add]
  constructor
  · rintro ⟨h₁, h₂⟩
    funext i
    cases i with
    | inl a => exact congrFun h₁ a
    | inr a => exact congrFun h₂ a
  · intro h
    exact ⟨funext fun a => congrFun h (Sum.inl a), funext fun a => congrFun h (Sum.inr a)⟩

variable [DecidableEq n]

set_option backward.isDefEq.respectTransparency false in
/-- Given the free identification of identity gluing, the original patch splits off a
finite free module. The complementary patch uses the inverse transition matrix. -/
theorem exists_split (hq : Function.Surjective q) (U : GL n D)
    (identity : patch q s (1 : Matrix (n ⊕ n) (n ⊕ n) D) ≃ₗ[A] ((n ⊕ n) → A)) :
    ∃ (i : patch q s U.val →ₗ[A] ((n ⊕ n) → A))
        (r : ((n ⊕ n) → A) →ₗ[A] patch q s U.val),
      r.comp i = LinearMap.id := by
  obtain ⟨V, hV⟩ := MilnorStabilizedMatrix.stabilized_lifts q.toRingHom hq U
  let e : (patch q s U.val × patch q s U.inv) ≃ₗ[A] ((n ⊕ n) → A) :=
    (blockPatchEquiv q s U.val U.inv).trans
      ((equivOfLift q s (MilnorStabilizedMatrix.stabilized U) V hV).trans identity)
  refine ⟨e.toLinearMap.comp (LinearMap.inl A _ _),
     (LinearMap.fst A _ _).comp e.symm.toLinearMap, ?_⟩
  apply LinearMap.ext
  intro x
  change (e.symm (e (x, 0))).1 = x
  rw [e.symm_apply_apply]

/-- The coordinate patch is finite and projective when identity gluing is the free patch. -/
theorem finite_projective_of_identity (hq : Function.Surjective q) (U : GL n D)
    (identity : patch q s (1 : Matrix (n ⊕ n) (n ⊕ n) D) ≃ₗ[A] ((n ⊕ n) → A)) :
    Module.Finite A (patch q s U.val) ∧ Module.Projective A (patch q s U.val) := by
  letI : Module.Finite A ((n ⊕ n) → A) := Module.Finite.of_basis (Pi.basisFun A (n ⊕ n))
  letI : Module.Projective A ((n ⊕ n) → A) := Module.Projective.of_basis (Pi.basisFun A (n ⊕ n))
  obtain ⟨i, r, hir⟩ := exists_split q s hq U identity
  have hr : Function.Surjective r := fun x => ⟨i x, DFunLike.congr_fun hir x⟩
  exact ⟨Module.Finite.of_surjective r hr, Module.Projective.of_split i r hir⟩

end ManuscriptAudit.MilnorProjectivePatch

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.MilnorProjectivePatch.blockPatchEquiv,
      ``ManuscriptAudit.MilnorProjectivePatch.exists_split,
      ``ManuscriptAudit.MilnorProjectivePatch.finite_projective_of_identity] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
