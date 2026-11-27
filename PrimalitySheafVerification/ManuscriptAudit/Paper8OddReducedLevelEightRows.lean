import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossCuspNormalization

/-!
# The odd reduced-row sign as a level-eight cross-cusp character

For D=2k with k odd, the cusp representative [1 0;2 1] gives a unique
right translate modulo two whose level matrix lies in Γ₀(8). The lower
right character of that matrix is precisely the mod-four character
of k.
-/

namespace ManuscriptAudit.Paper8OddReducedLevelEightRows

open Matrix Paper8NormalizedKloostermanRows Paper8OddCrossCuspRows
open Paper8OddCrossCuspNormalization (rightTranslation_entries)
open scoped MatrixGroups

def halfCuspMatrix : SL(2, ℤ) :=
  ⟨!![1, 0; 2, 1], by norm_num [Matrix.det_fin_two_of]⟩

def halfTranslate (A : SL(2, ℤ)) (m : ℤ) : SL(2, ℤ) :=
  A * ModularGroup.T ^ m * halfCuspMatrix⁻¹

theorem halfTranslate_entries (A : SL(2, ℤ)) (m : ℤ) :
    halfTranslate A m 1 0 = A 1 0 - 2 * (A 1 1 + A 1 0 * m) ∧
    halfTranslate A m 1 1 = A 1 1 + A 1 0 * m := by
  have hInv : (halfCuspMatrix⁻¹).1 = (!![1, 0; -2, 1] : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [halfCuspMatrix]
  have hE := rightTranslation_entries A m
  let B := A * ModularGroup.T ^ m
  constructor
  · change (B.1 * (halfCuspMatrix⁻¹).1) 1 0 = _
    rw [hInv]
    simp [Matrix.mul_apply, Fin.sum_univ_two, hE.2.1, hE.2.2, B] <;> ring
  · change (B.1 * (halfCuspMatrix⁻¹).1) 1 1 = _
    rw [hInv]
    simp [Matrix.mul_apply, Fin.sum_univ_two, hE.2.2, B]

theorem levelEight_iff {k : ℕ} (A : NormalizedRow (2 * k)) (m : ℤ) :
    halfTranslate A.1 m ∈ CongruenceSubgroup.Gamma0 8 ↔
      (4 : ℤ) ∣ (k : ℤ) - (A.1 1 1 + 2 * (k : ℤ) * m) := by
  rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd,
    (halfTranslate_entries A.1 m).1, A.property.1, Nat.cast_mul, Nat.cast_ofNat]
  have hEq : 2 * (k : ℤ) - 2 * (A.1 1 1 + 2 * (k : ℤ) * m) =
      2 * ((k : ℤ) - (A.1 1 1 + 2 * (k : ℤ) * m)) := by ring
  rw [hEq]
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q, by linarith⟩
  · rintro ⟨q, hq⟩
    exact ⟨q, by linarith⟩

theorem unique_halfTranslate {k : ℕ} (hk : Odd k) (A : NormalizedRow (2 * k)) :
    ∃! m : Fin 2, halfTranslate A.1 (m.val : ℤ) ∈ CongruenceSubgroup.Gamma0 8 := by
  have hd := (bottom A).property
  have hdOdd : Odd (bottom A).1.val := (hd.of_dvd_right (dvd_mul_right 2 k)).odd_of_right
  obtain ⟨a, ha⟩ := hk
  obtain ⟨b, hb⟩ := hdOdd
  have hIntA : (k : ℤ) = 2 * (a : ℤ) + 1 := by exact_mod_cast ha
  have hIntB : A.1 1 1 = 2 * (b : ℤ) + 1 := by
    rw [← bottom_cast A]
    exact_mod_cast hb
  have hCut : (4 : ℤ) ∣ (k : ℤ) - A.1 1 1 ↔
      ¬(4 : ℤ) ∣ (k : ℤ) - (A.1 1 1 + 2 * (k : ℤ)) := by
    omega
  by_cases h : (4 : ℤ) ∣ (k : ℤ) - A.1 1 1
  · refine ⟨0, (levelEight_iff A _).2 (by simpa using h), fun t ht => ?_⟩
    have ht' := (levelEight_iff A _).1 ht
    fin_cases t
    · rfl
    · exact ((hCut.mp h) (by simpa using ht')).elim
  · have hAlt : (4 : ℤ) ∣ (k : ℤ) - (A.1 1 1 + 2 * (k : ℤ)) := by
      by_contra hn
      exact h (hCut.mpr hn)
    refine ⟨1, (levelEight_iff A _).2 (by simpa using hAlt), fun t ht => ?_⟩
    have ht' := (levelEight_iff A _).1 ht
    fin_cases t
    · exact (h (by simpa using ht')).elim
    · rfl

theorem halfTranslate_character {k : ℕ} (A : NormalizedRow (2 * k)) (m : ℤ)
    (hm : halfTranslate A.1 m ∈ CongruenceSubgroup.Gamma0 8) :
    chiFour (halfTranslate A.1 m 1 1 : ZMod 4) = chiFour (k : ZMod 4) := by
  have hf := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).2 ((levelEight_iff A m).1 hm)
  rw [Int.cast_sub, sub_eq_zero] at hf
  rw [(halfTranslate_entries A.1 m).2, A.property.1, Nat.cast_mul, Nat.cast_ofNat]
  exact congrArg chiFour hf.symm

end ManuscriptAudit.Paper8OddReducedLevelEightRows

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8OddReducedLevelEightRows.halfTranslate_entries,
      ``ManuscriptAudit.Paper8OddReducedLevelEightRows.levelEight_iff,
      ``ManuscriptAudit.Paper8OddReducedLevelEightRows.unique_halfTranslate,
      ``ManuscriptAudit.Paper8OddReducedLevelEightRows.halfTranslate_character] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
