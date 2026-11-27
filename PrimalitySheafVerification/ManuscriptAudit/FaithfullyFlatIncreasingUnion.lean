import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import PrimalitySheafVerification.ManuscriptAudit.FlatIncreasingUnion

/-! An exhaustive increasing union of faithfully flat subalgebras is
faithfully flat. Membership in an extended ideal is already witnessed
inside one finite stage. -/

namespace ManuscriptAudit.FaithfullyFlatIncreasingUnion

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
variable (U : ℕ → Subalgebra R B)
variable (hMono : Monotone U) (hCover : ∀ b : B, ∃ n, b ∈ U n)

private theorem transport_ideal (I : Ideal R) {m n : ℕ} (h : m ≤ n) (b : U m)
    (hb : b ∈ I.map (algebraMap R (U m))) :
    (Subalgebra.inclusion (hMono h) b) ∈ I.map (algebraMap R (U n)) := by
  let a := Subalgebra.inclusion (hMono h)
  have hcomp : a.toRingHom.comp (algebraMap R (U m)) = algebraMap R (U n) :=
    RingHom.ext a.commutes
  have hba := Ideal.mem_map_of_mem a.toRingHom hb
  rw [Ideal.map_map, hcomp] at hba
  exact hba

include hMono hCover in
theorem ideal_mem_exists_stage (I : Ideal R) (b : B) (hb : b ∈ I.map (algebraMap R B)) :
    ∃ n, ∃ z : U n, z ∈ I.map (algebraMap R (U n)) ∧ (z : B) = b := by
  change b ∈ Submodule.span B ((algebraMap R B) '' (I : Set R)) at hb
  induction hb using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨0, algebraMap R (U 0) a, Ideal.mem_map_of_mem _ ha, rfl⟩
  | zero =>
    exact ⟨0, 0, (I.map (algebraMap R (U 0))).zero_mem, rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, a, ha, rfl⟩ := hx
    obtain ⟨n, b, hb, rfl⟩ := hy
    let a' := Subalgebra.inclusion (hMono (Nat.le_max_left m n)) a
    let b' := Subalgebra.inclusion (hMono (Nat.le_max_right m n)) b
    refine ⟨max m n, a' + b', ?_, rfl⟩
    exact Ideal.add_mem _ (transport_ideal U hMono I (Nat.le_max_left m n) a ha)
      (transport_ideal U hMono I (Nat.le_max_right m n) b hb)
  | smul a x _ hx =>
    obtain ⟨m, hm⟩ := hCover a
    obtain ⟨n, b, hb, rfl⟩ := hx
    let a' : U (max m n) := ⟨a, hMono (Nat.le_max_left m n) hm⟩
    let b' := Subalgebra.inclusion (hMono (Nat.le_max_right m n)) b
    refine ⟨max m n, a' * b', ?_, rfl⟩
    exact Ideal.mul_mem_left _ a' (transport_ideal U hMono I (Nat.le_max_right m n) b hb)

include hMono hCover in
theorem faithfullyFlat (hStages : ∀ n, Module.FaithfullyFlat R (U n)) :
    Module.FaithfullyFlat R B := by
  apply (Module.FaithfullyFlat.iff_flat_and_proper_ideal R B).mpr
  refine ⟨?_, ?_⟩
  · apply FlatIncreasingUnion.flat_of_exhaustion (fun n ↦ (U n).toSubmodule) hMono hCover
    intro n
    exact (hStages n).toFlat
  · intro I hI hTop
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_eq_top_iff] at hTop
    have hOne : (1 : B) ∈ I.map (algebraMap R B) :=
      (Ideal.eq_top_iff_one _).mp hTop
    obtain ⟨n, z, hZn, hz⟩ := ideal_mem_exists_stage U hMono hCover I 1 hOne
    have hZ : z = 1 := Subtype.ext hz
    subst z
    letI := hStages n
    apply hI
    apply (Ideal.eq_top_iff_one _).mpr
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := U n) I]
    change algebraMap R (U n) 1 ∈ I.map (algebraMap R (U n))
    simpa only [map_one] using hZn

end

end ManuscriptAudit.FaithfullyFlatIncreasingUnion

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.FaithfullyFlatIncreasingUnion.ideal_mem_exists_stage,
      ``ManuscriptAudit.FaithfullyFlatIncreasingUnion.faithfullyFlat] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
