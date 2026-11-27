import Lean.Util.CollectAxioms
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-! The algebra tensor square of an increasing union is exhausted by
the genuine maps from the tensor squares of its stages. -/

namespace ManuscriptAudit.TensorSquareIncreasingUnion

open scoped TensorProduct
open Algebra.TensorProduct

noncomputable section

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
variable (U : ℕ → Subalgebra R B)

/-- Actual tensor-square map induced by the two stage inclusions. -/
def stageTensor (n : ℕ) : (U n ⊗[R] U n) →ₐ[R] (B ⊗[R] B) :=
  Algebra.TensorProduct.map (U n).val (U n).val

private theorem stageTensor_comp {m n : ℕ} (h : U m ≤ U n) :
    (stageTensor U n).comp (Algebra.TensorProduct.map (Subalgebra.inclusion h) (Subalgebra.inclusion h)) =
      stageTensor U m := by
  rw [stageTensor, ← Algebra.TensorProduct.map_comp, Subalgebra.val_comp_inclusion]
  rfl

theorem range_mono (hMono : Monotone U) :
    Monotone (fun n ↦ (stageTensor U n).range) := by
  intro n m h x hx
  obtain ⟨z, rfl⟩ := hx
  let i := Subalgebra.inclusion (hMono h)
  refine ⟨Algebra.TensorProduct.map i i z, ?_⟩
  exact AlgHom.congr_fun (stageTensor_comp U (hMono h)) z

/-- Each element of the genuine tensor square comes from one stage. -/
theorem exists_tensor_stage (hMono : Monotone U) (hCover : ∀ b : B, ∃ n, b ∈ U n)
    (z : B ⊗[R] B) : ∃ n, ∃ w : U n ⊗[R] U n, stageTensor U n w = z := by
  induction z using TensorProduct.induction_on with
  | zero =>
    exact ⟨0, 0, map_zero _⟩
  | tmul x y =>
    obtain ⟨m, hm⟩ := hCover x
    obtain ⟨n, hn⟩ := hCover y
    let w := max m n
    let x' : U w := ⟨x, hMono (le_max_left _ _) hm⟩
    let y' : U w := ⟨y, hMono (le_max_right _ _) hn⟩
    exact ⟨w, x' ⊗ₜ[R] y', Algebra.TensorProduct.map_tmul _ _ _ _⟩
  | add x y hx hy =>
    obtain ⟨m, u, hu⟩ := hx
    obtain ⟨n, v, hv⟩ := hy
    let w := max m n
    obtain ⟨u', hu'⟩ := range_mono U hMono (le_max_left m n) (show x ∈ (stageTensor U m).range from ⟨u, hu⟩)
    obtain ⟨v', hv'⟩ := range_mono U hMono (le_max_right m n) (show y ∈ (stageTensor U n).range from ⟨v, hv⟩)
    exact ⟨w, u' + v', by rw [map_add, hu', hv']⟩

/-- Multiplication on the square commutes with the actual stage inclusion. -/
theorem multiplication_comp (n : ℕ) :
    (Algebra.TensorProduct.lmul' R).comp (stageTensor U n) =
      (U n).val.comp (Algebra.TensorProduct.lmul' R) := by
  apply Algebra.TensorProduct.ext'
  intro x y
  simp only [stageTensor, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.lmul'_apply_tmul, map_mul]

end
end ManuscriptAudit.TensorSquareIncreasingUnion

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.TensorSquareIncreasingUnion.exists_tensor_stage,
      ``ManuscriptAudit.TensorSquareIncreasingUnion.multiplication_comp] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
