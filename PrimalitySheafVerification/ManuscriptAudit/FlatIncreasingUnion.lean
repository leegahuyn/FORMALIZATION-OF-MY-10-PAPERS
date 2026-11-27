import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Flat.EquationalCriterion

/-! An increasing union of flat submodules is flat. A finite linear relation
can be resolved in a single stage via the equational criterion. -/

namespace ManuscriptAudit.FlatIncreasingUnion

noncomputable section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Flatness for an exhaustive increasing sequence of actual submodules. -/
theorem flat_of_exhaustion (P : ℕ → Submodule R M) (hMono : Monotone P)
    (hCover : ∀ x : M, ∃ n : ℕ, x ∈ P n) (hFlat : ∀ n, Module.Flat R (P n)) :
    Module.Flat R M := by
  classical
  apply Module.Flat.of_forall_isTrivialRelation
  intro l f x hx
  choose stage hStage using fun i : Fin l ↦ hCover (x i)
  let n := Finset.univ.sup stage
  let y (i : Fin l) : P n :=
    ⟨x i, hMono (Finset.le_sup (f := stage) (Finset.mem_univ i)) (hStage i)⟩
  let inc := (P n).subtype
  have hy : ∑ i, f i • y i = 0 := by
    apply (P n).subtype_injective
    simpa only [map_sum, map_smul, map_zero, inc, y, Submodule.subtype_apply] using hx
  letI := hFlat n
  obtain ⟨k, a, z, hz, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hy
  refine ⟨k, a, fun j ↦ (z j).val, fun i ↦ ?_, ha⟩
  have h := congrArg inc (hz i)
  simpa only [map_sum, map_smul, inc, y, Submodule.subtype_apply] using h

end
end ManuscriptAudit.FlatIncreasingUnion

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.FlatIncreasingUnion.flat_of_exhaustion
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
