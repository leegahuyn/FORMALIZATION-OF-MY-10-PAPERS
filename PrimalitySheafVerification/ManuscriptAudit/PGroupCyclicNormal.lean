import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# A smaller quotient of a finite nontrivial p-group

A nonidentity element in the center generates a nontrivial normal
cyclic subgroup, and the quotient has smaller cardinality.
-/

namespace ManuscriptAudit.PGroupCyclicNormal

/-- A finite nontrivial p-group has a central cyclic subgroup with a
strictly smaller quotient. -/
theorem exists_cyclic_normal_smaller {G : Type*} [Group G] [Finite G] [Nontrivial G]
    {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G) :
    ∃ S : Subgroup G, S.Normal ∧ IsCyclic S ∧ Nat.card (G ⧸ S) < Nat.card G := by
  letI : Nontrivial (Subgroup.center G) := hG.center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center G)
  let S := Subgroup.zpowers (z : G)
  have hz' : (z : G) ≠ 1 := fun h ↦ hz (Subtype.ext h)
  have hle : S ≤ Subgroup.center G := Subgroup.zpowers_le.mpr z.property
  have hNormal : S.Normal := ⟨fun y hy x ↦ by
    rw [Subgroup.mem_center_iff.mp (hle hy) x, mul_assoc, mul_inv_cancel, mul_one]
    exact hy⟩
  have hCard : 1 < Nat.card S :=
    S.one_lt_card_iff_ne_bot.mpr (Subgroup.zpowers_ne_bot.mpr hz')
  refine ⟨S, hNormal, inferInstance, ?_⟩
  have hPos : 0 < Nat.card (G ⧸ S) := Nat.card_pos
  calc
    Nat.card (G ⧸ S) = 1 * Nat.card (G ⧸ S) := (one_mul _).symm
    _ < Nat.card S * Nat.card (G ⧸ S) := Nat.mul_lt_mul_of_pos_right hCard hPos
    _ = Nat.card G := S.card_mul_index

end ManuscriptAudit.PGroupCyclicNormal

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.PGroupCyclicNormal.exists_cyclic_normal_smaller
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
