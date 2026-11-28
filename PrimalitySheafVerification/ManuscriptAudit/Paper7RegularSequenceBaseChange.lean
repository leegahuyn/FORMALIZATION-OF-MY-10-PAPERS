import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! Positive rank-one differentials commute with every scalar extension.
Flat extension preserves the actual successive nonzerodivisor conditions,
and a faithfully flat extension also detects them. -/

namespace ManuscriptAudit.Paper7RegularSequenceBaseChange

open RingTheory.Sequence Submodule
open scoped TensorProduct

noncomputable section

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]

section Differential

variable (M : Type*) [AddCommGroup M] [Module R M]

/-- The actual degree-one Koszul boundary becomes multiplication by
the image parameter after tensoring, with no flatness premise. -/
theorem boundary_baseChange (a : R) :
    AlgebraTensorModule.lTensor S S (a • (LinearMap.id : M →ₗ[R] M)) =
      algebraMap R S a • (LinearMap.id : S ⊗[R] M →ₗ[S] S ⊗[R] M) := by
  apply LinearMap.ext
  intro z
  induction z with
  | zero => simp
  | tmul s m =>
      rw [AlgebraTensorModule.lTensor_tmul, LinearMap.smul_apply, LinearMap.id_apply,
        LinearMap.smul_apply, LinearMap.id_apply, ← TensorProduct.smul_tmul]
      rw [TensorProduct.smul_tmul', Algebra.smul_def, smul_eq_mul]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end Differential

/-- Every member of a flat base-changed weakly regular sequence is a
nonzerodivisor on the true previous quotient over the new ring. -/
theorem preserves_weak [Module.Flat R S] {M : Type*} [AddCommGroup M] [Module R M]
    (xs : List R) (h : IsWeaklyRegular M xs) :
    IsWeaklyRegular (S ⊗[R] M) (xs.map (algebraMap R S)) :=
  (isWeaklyRegular_map_algebraMap_iff S (S ⊗[R] M) xs).mpr
    (h.isWeaklyRegular_lTensor (M₂ := S))

/-- Faithfully flat tensoring detects the original nonzerodivisor conditions
on every successive quotient. -/
theorem detects_weak [Module.FaithfullyFlat R S] (xs : List R) :
    ∀ (M : Type*) [AddCommGroup M] [Module R M],
      IsWeaklyRegular (S ⊗[R] M) xs → IsWeaklyRegular M xs := by
  induction xs with
  | nil =>
      intro M _ _ _
      exact IsWeaklyRegular.nil R M
  | cons x xs ih =>
      intro M _ _ h
      obtain ⟨hReg, hTail⟩ := (isWeaklyRegular_cons_iff (S ⊗[R] M) x xs).mp h
      have hx : IsSMulRegular M x := by
        apply (Module.FaithfullyFlat.lTensor_injective_iff_injective R S).mp
          (f := DistribSMul.toLinearMap R M x)
        rw [LinearMap.lTensor_smul_action]
        exact hReg
      let e := tensorQuotSMulTopEquivQuotSMulTop x S M
      exact (isWeaklyRegular_cons_iff M x xs).mpr
        ⟨hx, ih (QuotSMulTop x M) ((e.isWeaklyRegular_congr xs).mpr hTail)⟩

theorem faithfullyFlat_weak_iff [Module.FaithfullyFlat R S] {M : Type*}
    [AddCommGroup M] [Module R M] (xs : List R) :
    IsWeaklyRegular (S ⊗[R] M) (xs.map (algebraMap R S)) ↔ IsWeaklyRegular M xs := by
  constructor
  · intro h
    exact detects_weak R S xs M
      ((isWeaklyRegular_map_algebraMap_iff S (S ⊗[R] M) xs).mp h)
  · exact preserves_weak R S xs

end
end ManuscriptAudit.Paper7RegularSequenceBaseChange

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.Paper7RegularSequenceBaseChange.boundary_baseChange,
      ``ManuscriptAudit.Paper7RegularSequenceBaseChange.preserves_weak,
      ``ManuscriptAudit.Paper7RegularSequenceBaseChange.faithfullyFlat_weak_iff] do
    let ax ← collectAxioms name
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
