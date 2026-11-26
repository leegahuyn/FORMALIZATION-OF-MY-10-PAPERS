import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CertifiedTorsorSplit
import PrimalitySheafVerification.ManuscriptAudit.CertifiedTorsorSplitTrace

/-!
# Split affine trace after a section of the base-changed cover

The geometric section is induced by an algebra map from the original
cover algebra to the new base algebra.
-/

namespace ManuscriptAudit.CertifiedTorsorBaseChangeSplitTrace

open InvolutionTensorComparison InvolutionTensorBaseChange CertifiedTorsorSpectrumTrace
open scoped TensorProduct

noncomputable section

universe u v

variable (A E R : Type u) [CommRing A] [CommRing E] [CommRing R] [Algebra A E] [Algebra A R]
variable (M : Type v) [TopologicalSpace M] [AddCommGroup M] [IsTopologicalAddGroup M]

theorem surjective (σ : E ≃ₐ[A] E) (hσ : Function.Involutive σ)
    (c : CertifiedComparison A E σ) (g : E →ₐ[A] R)
    (hσR : Function.Involutive (baseSwap A E R σ))
    (cR : CertifiedComparison R (R ⊗[A] E) (baseSwap A E R σ))
    (hf : Module.Finite R (R ⊗[A] E)) (hff : Module.FaithfullyFlat R (R ⊗[A] E)) :
    Function.Surjective (spectrumTrace R (R ⊗[A] E) (M := M) (baseSwap A E R σ) hσR cR hf hff) := by
  letI : Algebra E R := g.toRingHom.toAlgebra
  letI : IsScalarTower A E R := IsScalarTower.of_algHom g
  let e := CertifiedTorsorSplit.firstIdempotent A E R σ c
  let f := CertifiedTorsorSplit.secondIdempotent A E R σ c
  exact spectrumTrace_surjective_of_idempotents R (R ⊗[A] E) (M := M) (baseSwap A E R σ)
    hσR cR hf hff e f (CertifiedTorsorSplit.idempotents_mul A E R σ c)
    (CertifiedTorsorSplit.idempotents_add A E R σ c)
    (CertifiedTorsorSplit.deck_firstIdempotent A E R σ c hσ)

end

end ManuscriptAudit.CertifiedTorsorBaseChangeSplitTrace

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CertifiedTorsorBaseChangeSplitTrace.surjective
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter (fun axiomName => !allowed.contains axiomName)
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
