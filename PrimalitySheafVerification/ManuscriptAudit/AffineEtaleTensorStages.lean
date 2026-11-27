import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! The genuine finite tensor stages attached to a sequence of faithfully
flat étale affine covers, with their actual algebra inclusions. -/

namespace ManuscriptAudit.AffineEtaleTensorStages

open CategoryTheory
open scoped TensorProduct

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {R : Type u} [CommRing R] (B : ℕ → CommAlgCat.{u} R)

def stage : ℕ → CommAlgCat.{u} R
  | 0 => CommAlgCat.of R R
  | n + 1 => CommAlgCat.of R ((stage n) ⊗[R] (B n))

/-- The actual transition inclusion into the next tensor stage. -/
def step (n : ℕ) : stage B n ⟶ stage B (n + 1) :=
  CommAlgCat.ofHom (Algebra.TensorProduct.includeLeft : (stage B n) →ₐ[R] (stage B n) ⊗[R] (B n))

/-- The actual factor from the new cover to its first tensor stage. -/
def factor (n : ℕ) : B n ⟶ stage B (n + 1) :=
  CommAlgCat.ofHom (Algebra.TensorProduct.includeRight : (B n) →ₐ[R] (stage B n) ⊗[R] (B n))

theorem stage_etale (h : ∀ n, Algebra.Etale R (B n)) (n : ℕ) :
    Algebra.Etale R (stage B n) := by
  induction n with
  | zero => exact inferInstanceAs (Algebra.Etale R R)
  | succ n ih =>
    letI : Algebra.Etale R (stage B n) := ih
    letI : Algebra.Etale R (B n) := h n
    change Algebra.Etale R ((stage B n) ⊗[R] (B n))
    exact Algebra.Etale.comp R (stage B n) _

theorem stage_faithfullyFlat (h : ∀ n, Module.FaithfullyFlat R (B n)) (n : ℕ) :
    Module.FaithfullyFlat R (stage B n) := by
  induction n with
  | zero => exact inferInstanceAs (Module.FaithfullyFlat R R)
  | succ n ih =>
    letI : Module.FaithfullyFlat R (stage B n) := ih
    letI : Module.FaithfullyFlat R (B n) := h n
    change Module.FaithfullyFlat R ((stage B n) ⊗[R] (B n))
    exact Module.FaithfullyFlat.trans R (stage B n) ((stage B n) ⊗[R] (B n))

theorem step_injective (h : ∀ n, Module.FaithfullyFlat R (B n)) (n : ℕ) :
    Function.Injective (step B n).hom := by
  letI : Module.FaithfullyFlat R (B n) := h n
  change Function.Injective (algebraMap (stage B n) ((stage B n) ⊗[R] (B n)))
  exact FaithfulSMul.algebraMap_injective _ _

end

end ManuscriptAudit.AffineEtaleTensorStages

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleTensorStages.stage_etale,
      ``ManuscriptAudit.AffineEtaleTensorStages.stage_faithfullyFlat,
      ``ManuscriptAudit.AffineEtaleTensorStages.step_injective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
