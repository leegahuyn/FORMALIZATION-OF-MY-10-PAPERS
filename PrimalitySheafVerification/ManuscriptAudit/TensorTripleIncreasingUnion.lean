import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.FlatTensorStageInjections

/-! Finite Čech degree-two affine terms descend to an actual stage of an increasing union. -/

namespace ManuscriptAudit.TensorTripleIncreasingUnion

open scoped TensorProduct
open TensorSquareIncreasingUnion (stageTensor exists_tensor_stage)
open FlatTensorStageInjections (stageTriple)

noncomputable section

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
variable (U : ℕ → Subalgebra R B)

private theorem stageSquare_comp {n m : ℕ} (h : U n ≤ U m) :
    (stageTensor U m).comp (Algebra.TensorProduct.map (Subalgebra.inclusion h) (Subalgebra.inclusion h)) =
      stageTensor U n := by
  rw [stageTensor, ← Algebra.TensorProduct.map_comp, Subalgebra.val_comp_inclusion]
  rfl

private theorem stageTriple_comp {n m : ℕ} (h : U n ≤ U m) :
    (stageTriple U m).comp (Algebra.TensorProduct.map
      (Algebra.TensorProduct.map (Subalgebra.inclusion h) (Subalgebra.inclusion h))
      (Subalgebra.inclusion h)) = stageTriple U n := by
  rw [stageTriple, ← Algebra.TensorProduct.map_comp, stageSquare_comp, Subalgebra.val_comp_inclusion]
  rfl

/-- Threefold tensor ranges form the actual increasing family. -/
theorem range_mono (hMono : Monotone U) : Monotone (fun n => (stageTriple U n).range) := by
  intro n m h x hx
  obtain ⟨z, rfl⟩ := hx
  let i := Subalgebra.inclusion (hMono h)
  refine ⟨Algebra.TensorProduct.map (Algebra.TensorProduct.map i i) i z, ?_⟩
  exact AlgHom.congr_fun (stageTriple_comp U (hMono h)) z

/-- Every section of the literal threefold coordinate tensor product reaches a finite stage. -/
theorem exists_triple_stage (hMono : Monotone U) (hCover : ∀ b : B, ∃ n, b ∈ U n)
    (z : (B ⊗[R] B) ⊗[R] B) :
    ∃ n, ∃ w : (U n ⊗[R] U n) ⊗[R] U n, stageTriple U n w = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, map_zero _⟩
  | tmul x y =>
    obtain ⟨n, x', hx⟩ := exists_tensor_stage U hMono hCover x
    obtain ⟨m, hy⟩ := hCover y
    let w := max n m
    obtain ⟨x'', hx'⟩ := TensorSquareIncreasingUnion.range_mono U hMono (le_max_left n m)
      (show x ∈ (stageTensor U n).range from ⟨x', hx⟩)
    let y' : U w := ⟨y, hMono (le_max_right n m) hy⟩
    have hs : stageTensor U w x'' = x := hx'
    refine ⟨w, x'' ⊗ₜ[R] y', ?_⟩
    rw [stageTriple, Algebra.TensorProduct.map_tmul, hs] <;> rfl
  | add x y hx hy =>
    obtain ⟨n, x', hx'⟩ := hx
    obtain ⟨m, y', hy'⟩ := hy
    let w := max n m
    obtain ⟨x'', hX⟩ := range_mono U hMono (le_max_left n m)
      (show x ∈ (stageTriple U n).range from ⟨x', hx'⟩)
    obtain ⟨y'', hY⟩ := range_mono U hMono (le_max_right n m)
      (show y ∈ (stageTriple U m).range from ⟨y', hy'⟩)
    refine ⟨w, x'' + y'', ?_⟩
    exact (map_add (stageTriple U w) x'' y'').trans (congrArg₂ (·+·) hX hY)

end
end ManuscriptAudit.TensorTripleIncreasingUnion

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.TensorTripleIncreasingUnion.exists_triple_stage
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
