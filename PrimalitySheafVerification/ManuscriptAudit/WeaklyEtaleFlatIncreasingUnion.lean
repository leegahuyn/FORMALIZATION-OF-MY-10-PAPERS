import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.FlatQuotientLocalIdentities
import PrimalitySheafVerification.ManuscriptAudit.WeaklyEtaleIncreasingUnion

/-! Weak étaleness of an exhaustive increasing union of weakly étale subalgebras. -/

namespace ManuscriptAudit.WeaklyEtaleFlatIncreasingUnion

open AlgebraicGeometry CategoryTheory
open Algebra.TensorProduct
open scoped TensorProduct

noncomputable section

universe u
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
variable (U : ℕ → Subalgebra R B)
variable (hMono : Monotone U) (hCover : ∀ b : B, ∃ n, b ∈ U n)

private abbrev multiplication (A : Type u) [CommRing A] [Algebra R A] :
    A ⊗[R] A →ₐ[R] A :=
  Algebra.TensorProduct.lmul' (S := A) R

private theorem multiplication_surjective (A : Type u) [CommRing A] [Algebra R A] :
    Function.Surjective (multiplication (R := R) A) := by
  intro a
  exact ⟨a ⊗ₜ[R] (1 : A), by
    change Algebra.TensorProduct.lmul' (S := A) R (a ⊗ₜ[R] (1 : A)) = a
    rw [lmul'_apply_tmul, mul_one]⟩

include hMono hCover in
theorem diagonal_flat_of_stage_flat
    (hDiag : ∀ n, (multiplication (R := R) (U n)).toRingHom.Flat) :
    (multiplication (R := R) B).toRingHom.Flat := by
  let μ := multiplication (R := R) B
  letI : Algebra (B ⊗[R] B) B := μ.toRingHom.toAlgebra
  have hLoc : IsLocalization (IdempotentKernelLocalization.denominators (B ⊗[R] B) B) B := by
    apply IdempotentKernelLocalization.isLocalization_of_local_identities
    · exact multiplication_surjective (R := R) B
    · intro x hx
      change μ x = 0 at hx
      obtain ⟨n, z, hz⟩ := TensorSquareIncreasingUnion.exists_tensor_stage U hMono hCover x
      let i := TensorSquareIncreasingUnion.stageTensor U n
      let A := U n
      let μ₀ := multiplication (R := R) A
      have hf (w : A ⊗[R] A) : μ (i w) = A.val (μ₀ w) :=
        AlgHom.congr_fun (TensorSquareIncreasingUnion.multiplication_comp U n) w
      have hz₀ : μ₀ z = 0 := by
        apply Subtype.ext
        change A.val (μ₀ z) = A.val 0
        rw [map_zero, ← hf, hz]
        exact hx
      letI : Algebra (A ⊗[R] A) A := μ₀.toRingHom.toAlgebra
      letI : Module.Flat (A ⊗[R] A) A :=
        RingHom.flat_algebraMap_iff.mp (hDiag n)
      obtain ⟨e, he, hIdentity⟩ := FlatQuotientLocalIdentities.exists_kernel_left_identity
        (multiplication_surjective (R := R) A) hz₀
      refine ⟨i e, ?_, ?_⟩
      · change μ (i e) = 0
        rw [hf]
        change A.val (μ₀ e) = 0
        rw [show μ₀ e = 0 from he, map_zero]
      · rw [← hz, ← map_mul, hIdentity]
  letI := hLoc
  exact RingHom.flat_algebraMap_iff.mpr
    (IsLocalization.flat B (IdempotentKernelLocalization.denominators (B ⊗[R] B) B))

private abbrev specMap (A : Type u) [CommRing A] [Algebra R A] :
    Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R A))

include hMono hCover in
theorem weaklyEtale (hStage : ∀ n, WeaklyEtale (specMap (R := R) (U n))) :
    WeaklyEtale (specMap (R := R) B) := by
  have hFlat : Module.Flat R B := by
    apply FlatIncreasingUnion.flat_of_exhaustion (fun n ↦ (U n).toSubmodule) hMono hCover
    intro n
    exact RingHom.flat_algebraMap_iff.mp (Flat.SpecMap_iff.mp (hStage n).flat)
  have hDiag : ∀ n, (multiplication (R := R) (U n)).toRingHom.Flat := by
    intro n
    have h := (hStage n).flat_diagonal
    change Flat (Limits.pullback.diagonal
      (Spec.map (CommRingCat.ofHom (algebraMap R (U n))))) at h
    rw [AlgebraicGeometry.diagonal_SpecMap] at h
    exact Flat.SpecMap_iff.mp h
  refine ⟨Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr hFlat), ?_⟩
  change Flat (Limits.pullback.diagonal (Spec.map (CommRingCat.ofHom (algebraMap R B))))
  rw [AlgebraicGeometry.diagonal_SpecMap]
  exact Flat.SpecMap_iff.mpr (diagonal_flat_of_stage_flat U hMono hCover hDiag)

end
end ManuscriptAudit.WeaklyEtaleFlatIncreasingUnion

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeaklyEtaleFlatIncreasingUnion.diagonal_flat_of_stage_flat,
      ``ManuscriptAudit.WeaklyEtaleFlatIncreasingUnion.weaklyEtale] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
