import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.RingHom.Flat
import PrimalitySheafVerification.ManuscriptAudit.IdempotentKernelLocalization
import PrimalitySheafVerification.ManuscriptAudit.TensorSquareIncreasingUnion

/-! The actual diagonal multiplication of an increasing union of étale
algebras is flat, by the idempotent kernels at the finite stages. -/

namespace ManuscriptAudit.TensorDiagonalFlatIncreasingUnion

open scoped TensorProduct
open Algebra.TensorProduct

noncomputable section

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
variable (U : ℕ → Subalgebra R B)
open TensorSquareIncreasingUnion (stageTensor exists_tensor_stage multiplication_comp)

private theorem multiplication_isLocalization
    (hMono : Monotone U) (hCover : ∀ b : B, ∃ n, b ∈ U n)
    (hEtale : ∀ n, Algebra.Etale R (U n)) :
    haveI : Algebra (B ⊗[R] B) B := (Algebra.TensorProduct.lmul' (S := B) R).toRingHom.toAlgebra
    IsLocalization (IdempotentKernelLocalization.denominators (B ⊗[R] B) B) B := by
  let μ := Algebra.TensorProduct.lmul' (S := B) R
  letI : Algebra (B ⊗[R] B) B := μ.toRingHom.toAlgebra
  apply IdempotentKernelLocalization.isLocalization_of_local_identities
  · intro b
    exact ⟨b ⊗ₜ[R] 1, by change μ (b ⊗ₜ[R] 1) = b; rw [lmul'_apply_tmul, mul_one]⟩
  · intro x hx
    change μ x = 0 at hx
    obtain ⟨n, z, hz⟩ := exists_tensor_stage U hMono hCover x
    let i := stageTensor U n
    let A := U n
    let μ₀ := Algebra.TensorProduct.lmul' (S := A) R
    let J := KaehlerDifferential.ideal R A
    have hf (w : A ⊗[R] A) : μ (i w) = A.val (μ₀ w) :=
      AlgHom.congr_fun (multiplication_comp U n) w
    have hz₀ : μ₀ z = 0 := by
      apply Subtype.ext
      change A.val (μ₀ z) = A.val 0
      rw [map_zero, ← hf, hz]
      exact hx
    letI := hEtale n
    have hJ : IsIdempotentElem J :=
      (Ideal.cotangent_subsingleton_iff J).mp (inferInstanceAs (Subsingleton Ω[A⁄R]))
    obtain ⟨e, he, hSpan⟩ :=
      (Ideal.isIdempotentElem_iff_of_fg J (KaehlerDifferential.ideal_fg R A)).mp hJ
    have hSpan' : J = Ideal.span ({e} : Set (A ⊗[R] A)) := hSpan
    have hzMem : z ∈ Ideal.span ({e} : Set (A ⊗[R] A)) := by
      rw [← hSpan']
      exact hz₀
    have he₀ : μ₀ e = 0 := by
      change e ∈ J
      rw [hSpan']
      exact Ideal.mem_span_singleton_self e
    have hm : e * z = z := by
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hzMem
      rw [← mul_assoc, mul_comm e a, mul_assoc, he]
    refine ⟨i e, ?_, ?_⟩
    · change μ (i e) = 0
      rw [hf, he₀, map_zero]
    · rw [← hz, ← map_mul, hm]

/-- The native multiplication defining the diagonal has a flat ring map. -/
theorem multiplication_flat
    (hMono : Monotone U) (hCover : ∀ b : B, ∃ n, b ∈ U n)
    (hEtale : ∀ n, Algebra.Etale R (U n)) :
    (Algebra.TensorProduct.lmul' (S := B) R).toRingHom.Flat := by
  letI : Algebra (B ⊗[R] B) B := (Algebra.TensorProduct.lmul' (S := B) R).toRingHom.toAlgebra
  letI := multiplication_isLocalization U hMono hCover hEtale
  exact RingHom.flat_algebraMap_iff.mpr
    (IsLocalization.flat B (IdempotentKernelLocalization.denominators (B ⊗[R] B) B))

end
end ManuscriptAudit.TensorDiagonalFlatIncreasingUnion

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.TensorDiagonalFlatIncreasingUnion.multiplication_flat
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
