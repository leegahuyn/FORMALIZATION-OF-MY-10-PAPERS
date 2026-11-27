import Lean.Util.CollectAxioms
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.GroupTheory.Index

/-!
# Exact integral indices of Γ₀(2) and Γ₀(4)

Right multiplication by the level subgroup fixes a primitive first
column up to a unit modulo the level. The coset equivalence is checked
on the finite residue rings and each class has an integral determinant
one representative.
-/

namespace ManuscriptAudit.Paper8EtaLevelIndices

open Matrix
open scoped MatrixGroups

private theorem det_mod (N : ℕ) (g : SL(2, ℤ)) :
    (g 0 0 : ZMod N) * (g 1 1 : ZMod N) - (g 0 1 : ZMod N) * (g 1 0 : ZMod N) = 1 := by
  have h : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using Matrix.SpecialLinearGroup.det_coe g
  simpa only [Int.cast_sub, Int.cast_mul, Int.cast_one] using
    congrArg (fun z : ℤ => (z : ZMod N)) h

private theorem inverseMul_lowerLeft (g h : SL(2, ℤ)) :
    (g⁻¹ * h) 1 0 = g 0 0 * h 1 0 - g 1 0 * h 0 0 := by
  change ((g⁻¹).1 * h.1) 1 0 = _
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem mem_level_iff_det (N : ℕ) (g h : SL(2, ℤ)) :
    g⁻¹ * h ∈ CongruenceSubgroup.Gamma0 N ↔
      (g 0 0 : ZMod N) * (h 1 0 : ZMod N) -
        (g 1 0 : ZMod N) * (h 0 0 : ZMod N) = 0 := by
  rw [CongruenceSubgroup.Gamma0_mem, inverseMul_lowerLeft, Int.cast_sub,
    Int.cast_mul, Int.cast_mul]

private def columnTwo (a c : ZMod 2) : Fin 3 :=
  if c = 0 then 0 else if a = 0 then 1 else 2

private def columnFour (a c : ZMod 4) : Fin 6 :=
  if c = 0 then 0 else if c = 2 then 1 else
    ⟨2 + (a * c).val, Nat.add_lt_add_left (ZMod.val_lt _) 2⟩

private abbrev primitive {N : ℕ} (a c : ZMod N) : Prop :=
  a * a = 1 ∨ c * c = 1

private theorem primitive_two :
    ∀ a b c d : ZMod 2, a * d - b * c = 1 → primitive a c := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
private theorem primitive_four :
    ∀ a b c d : ZMod 4, a * d - b * c = 1 → primitive a c := by
  decide

private theorem columnTwo_eq_iff :
    ∀ a c a' c' : ZMod 2, primitive a c → primitive a' c' →
      (columnTwo a c = columnTwo a' c' ↔ a * c' - c * a' = 0) := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
private theorem columnFour_eq_iff :
    ∀ a c a' c' : ZMod 4, primitive a c → primitive a' c' →
      (columnFour a c = columnFour a' c' ↔ a * c' - c * a' = 0) := by
  decide

private def representativeTwo (i : Fin 3) : SL(2, ℤ) :=
  ![(1 : SL(2, ℤ)),
    ⟨!![0, -1; 1, 0], by norm_num [Matrix.det_fin_two_of]⟩,
    ⟨!![1, -1; 1, 0], by norm_num [Matrix.det_fin_two_of]⟩] i

private def representativeFour (i : Fin 6) : SL(2, ℤ) :=
  ![(1 : SL(2, ℤ)),
    ⟨!![1, 0; 2, 1], by norm_num [Matrix.det_fin_two_of]⟩,
    ⟨!![0, -1; 1, 0], by norm_num [Matrix.det_fin_two_of]⟩,
    ⟨!![1, -1; 1, 0], by norm_num [Matrix.det_fin_two_of]⟩,
    ⟨!![2, -1; 1, 0], by norm_num [Matrix.det_fin_two_of]⟩,
    ⟨!![3, -1; 1, 0], by norm_num [Matrix.det_fin_two_of]⟩] i

private theorem index_of_column {N k : ℕ} (f : SL(2, ℤ) → Fin k)
    (hEq : ∀ g h : SL(2, ℤ), f g = f h ↔ g⁻¹ * h ∈ CongruenceSubgroup.Gamma0 N)
    (hf : Function.Surjective f) : (CongruenceSubgroup.Gamma0 N).index = k := by
  let H := CongruenceSubgroup.Gamma0 N
  let map : SL(2, ℤ) ⧸ H → Fin k :=
    Quotient.lift f (fun g h hh => (hEq g h).2
      (QuotientGroup.leftRel_apply.1 hh))
  have hInj : Function.Injective map := by
    intro x y hxy
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
    exact QuotientGroup.eq.mpr ((hEq g h).1 hxy)
  have hSurj : Function.Surjective map := by
    intro i
    obtain ⟨g, hg⟩ := hf i
    exact ⟨QuotientGroup.mk g, hg⟩
  exact Nat.card_eq_of_equiv_fin (Equiv.ofBijective map ⟨hInj, hSurj⟩)

theorem levelTwo_index : (CongruenceSubgroup.Gamma0 2).index = 3 := by
  apply index_of_column (fun g => columnTwo (g 0 0 : ZMod 2) (g 1 0 : ZMod 2))
  · intro g h
    rw [mem_level_iff_det]
    apply columnTwo_eq_iff
    · exact primitive_two _ _ _ _ (det_mod 2 g)
    · exact primitive_two _ _ _ _ (det_mod 2 h)
  · intro i
    refine ⟨representativeTwo i, ?_⟩
    fin_cases i <;> decide

theorem levelFour_index : (CongruenceSubgroup.Gamma0 4).index = 6 := by
  apply index_of_column (fun g => columnFour (g 0 0 : ZMod 4) (g 1 0 : ZMod 4))
  · intro g h
    rw [mem_level_iff_det]
    apply columnFour_eq_iff
    · exact primitive_four _ _ _ _ (det_mod 4 g)
    · exact primitive_four _ _ _ _ (det_mod 4 h)
  · intro i
    refine ⟨representativeFour i, ?_⟩
    fin_cases i <;> decide

end ManuscriptAudit.Paper8EtaLevelIndices

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8EtaLevelIndices.levelTwo_index,
      ``ManuscriptAudit.Paper8EtaLevelIndices.levelFour_index] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
