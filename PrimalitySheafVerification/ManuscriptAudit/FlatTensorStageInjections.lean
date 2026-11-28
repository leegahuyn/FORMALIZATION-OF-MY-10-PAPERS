import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Flat.Basic
import PrimalitySheafVerification.ManuscriptAudit.TensorSquareIncreasingUnion

/-! Injectivity of the actual flat affine tensor transition on double and triple products. -/

namespace ManuscriptAudit.FlatTensorStageInjections

open scoped TensorProduct
open TensorSquareIncreasingUnion (stageTensor)

noncomputable section

variable {R A A' B B' : Type*} [CommRing R]
  [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
  [Algebra R A] [Algebra R A'] [Algebra R B] [Algebra R B']

/-- The genuine algebra-tensor map is injective when the middle tensor factors are flat. -/
theorem map_injective [Module.Flat R A'] [Module.Flat R B]
    (f : A →ₐ[R] A') (g : B →ₐ[R] B')
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (Algebra.TensorProduct.map f g) := by
  have h : (Algebra.TensorProduct.map f g).toLinearMap =
      TensorProduct.map f.toLinearMap g.toLinearMap := by
    apply TensorProduct.ext'
    intro x y
    rfl
  change Function.Injective (Algebra.TensorProduct.map f g).toLinearMap
  rw [h]
  exact TensorProduct.map_injective_of_flat_flat f.toLinearMap g.toLinearMap hf hg

variable (U : ℕ → Subalgebra R B)

/-- The actual double-product tensor ring embeds into the limiting double product. -/
theorem stageTensor_injective (n : ℕ) [Module.Flat R B] [Module.Flat R (U n)] :
    Function.Injective (stageTensor U n) :=
  map_injective (U n).val (U n).val (U n).val_injective (U n).val_injective

/-- The actual triple-product ring map, with explicit associativity convention. -/
def stageTriple (n : ℕ) : ((U n ⊗[R] U n) ⊗[R] U n) →ₐ[R] ((B ⊗[R] B) ⊗[R] B) :=
  Algebra.TensorProduct.map (stageTensor U n) (U n).val

/-- The actual triple-product tensor ring also embeds under the indicated flatness. -/
theorem stageTriple_injective (n : ℕ) [Module.Flat R B] [Module.Flat R (U n)]
    [Module.Flat R (B ⊗[R] B)] : Function.Injective (stageTriple U n) :=
  map_injective (stageTensor U n) (U n).val (stageTensor_injective U n) (U n).val_injective

end
end ManuscriptAudit.FlatTensorStageInjections

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.FlatTensorStageInjections.map_injective,
      ``ManuscriptAudit.FlatTensorStageInjections.stageTensor_injective,
      ``ManuscriptAudit.FlatTensorStageInjections.stageTriple_injective] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
