import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import PrimalitySheafVerification.ManuscriptAudit.Paper7RegularSequenceBaseChange

/-! Faithfully flat extension detects full regularity including properness
of the last native quotient of the sequence. -/

namespace ManuscriptAudit.Paper7FaithfullyFlatRegularSequence

open RingTheory.Sequence
open scoped TensorProduct Pointwise

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
variable [Module.FaithfullyFlat R S]
variable {M : Type*} [AddCommGroup M] [Module R M]

/-- The full regular sequence condition is equivalent across a faithfully
flat scalar extension on the actual base-changed module. -/
theorem regular_iff (xs : List R) :
    IsRegular (S ⊗[R] M) (xs.map (algebraMap R S)) ↔ IsRegular M xs := by
  rw [isRegular_iff, isRegular_iff]
  refine and_congr (Paper7RegularSequenceBaseChange.faithfullyFlat_weak_iff R S xs) ?_
  let I := Ideal.ofList xs
  have e := TensorProduct.tensorQuotMapSMulEquivTensorQuot S M I
  have h : Nontrivial ((S ⊗[R] M) ⧸ I.map (algebraMap R S) • (⊤ : Submodule S (S ⊗[R] M))) ↔
      Nontrivial (M ⧸ (I • (⊤ : Submodule R M))) :=
    e.toEquiv.nontrivial_congr.trans (Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right R S)
  simpa only [I, Ideal.map_ofList, Submodule.Quotient.nontrivial_iff, ne_comm] using h

end ManuscriptAudit.Paper7FaithfullyFlatRegularSequence

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper7FaithfullyFlatRegularSequence.regular_iff
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{name} depends on unexpected axioms {ax}"
  logInfo m!"{name} uses {ax}"
