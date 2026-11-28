import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Rat.Floor
import Mathlib.Data.ZMod.Basic
import PrimalitySheafVerification.ManuscriptAudit.Paper8SawtoothDistribution

/-!
The finite residue permutation and rational moment identities underlying
Dedekind reciprocity. The floor expansion follows the finite-sum proof of
Eberl, Bordg, Paulson, and Li in the Archive of Formal Proofs.
-/

namespace ManuscriptAudit.Paper8DedekindResidueMoments

open Function Finset
open Paper8ContourResidueWeights Paper8SawtoothDistribution

noncomputable section

def residuePerm (h k : ℕ) (hk : 0 < k) (hC : h.Coprime k) : Fin k ≃ Fin k :=
  Equiv.ofBijective (fun j => ⟨(h * j.val) % k, Nat.mod_lt _ hk⟩)
    (by
      apply Finite.injective_iff_bijective.mp
      intro i j hij
      have hMod : (h * i.val) % k = (h * j.val) % k := congrArg Fin.val hij
      have hz := (ZMod.natCast_eq_natCast_iff' (h * i.val) (h * j.val) k).2 hMod
      rw [Nat.cast_mul, Nat.cast_mul] at hz
      let u := ZMod.unitOfCoprime h hC
      change (u : ZMod k) * (i.val : ZMod k) = (u : ZMod k) * (j.val : ZMod k) at hz
      have hx := congrArg (fun z : ZMod k => ((u⁻¹ : (ZMod k)ˣ) : ZMod k) * z) hz
      simp only [Units.inv_mul_cancel_left] at hx
      have hv := (ZMod.natCast_eq_natCast_iff' i.val j.val k).1 hx
      rw [Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at hv
      exact Fin.ext hv)

theorem residuePerm_val (h k : ℕ) (hk : 0 < k) (hC : h.Coprime k) (j : Fin k) :
    (residuePerm h k hk hC j).val = (h * j.val) % k := rfl

private theorem residuePerm_ne_zero (h k : ℕ) (hk : 0 < k) (hC : h.Coprime k)
    {j : Fin k} (hj : j.val ≠ 0) : (residuePerm h k hk hC j).val ≠ 0 := by
  let z : Fin k := ⟨0, hk⟩
  intro hz
  have he : residuePerm h k hk hC j = residuePerm h k hk hC z := by
    apply Fin.ext
    rw [hz, residuePerm_val]
    simp [z]
  apply hj
  exact congrArg Fin.val ((residuePerm h k hk hC).injective he)

theorem sawtooth_mul_eq_residue (h k : ℕ) (hk : 0 < k) (hC : h.Coprime k) (j : Fin k) :
    sawtooth ((h : ℚ) * (j.val : ℚ) / (k : ℚ)) =
      sawtooth (((residuePerm h k hk hC j).val : ℚ) / (k : ℚ)) := by
  let m := (h * j.val) / k
  have hM := Nat.mod_add_div (h * j.val) k
  have hQ := congrArg (fun n : ℕ => (n : ℚ)) hM
  push_cast at hQ
  have hK : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [residuePerm_val]
  have hEq : (h : ℚ) * (j.val : ℚ) / (k : ℚ) =
      (((h * j.val) % k : ℕ) : ℚ) / (k : ℚ) + (((m : ℕ) : ℤ) : ℚ) := by
    push_cast
    apply (div_eq_iff hK).2
    dsimp only [m]
    field_simp [hK] <;> nlinarith [hQ]
  rw [hEq, sawtooth_int_translate]

private theorem sawtooth_fin_ne_zero {k : ℕ} (hk : 0 < k) (j : Fin k) (hj : j.val ≠ 0) :
    sawtooth ((j.val : ℚ) / (k : ℚ)) = (j.val : ℚ) / (k : ℚ) - 1 / 2 := by
  have hK : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hk
  have hJ : (0 : ℚ) < (j.val : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hj
  have hJk : (j.val : ℚ) < (k : ℚ) := by exact_mod_cast j.isLt
  rw [sawtooth_on_unit (div_nonneg hJ.le hK.le) ((div_lt_one hK).2 hJk)]
  simp [ne_of_gt (div_pos hJ hK)]

private theorem sum_fin_val (k : ℕ) : ∑ j : Fin k, (j.val : ℚ) = (k : ℚ) * ((k : ℚ) - 1) / 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_succ, ih]
    ring

private theorem sum_fin_val_sq (k : ℕ) :
    ∑ j : Fin k, (j.val : ℚ) ^ 2 = (k : ℚ) * ((k : ℚ) - 1) * (2 * k - 1) / 6 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_succ, ih]
    ring

def fraction {k : ℕ} (j : Fin k) : ℚ := (j.val : ℚ) / (k : ℚ)

theorem sum_fraction {k : ℕ} (hk : 0 < k) :
    ∑ j : Fin k, fraction j = ((k : ℚ) - 1) / 2 := by
  have hn : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  simp only [fraction, ← Finset.sum_div, sum_fin_val]
  field_simp [hn] <;> ring

theorem sum_fraction_sq {k : ℕ} (hk : 0 < k) :
    ∑ j : Fin k, fraction j ^ 2 = ((k : ℚ) - 1) * (2 * k - 1) / (6 * k) := by
  have hn : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  simp only [fraction, div_pow, ← Finset.sum_div, sum_fin_val_sq]
  field_simp [hn] <;> ring

theorem dedekindSum_eq_fraction_product {h k : ℕ} (hk : 0 < k) (hC : h.Coprime k) :
    dedekindSum (h : ℤ) k =
      (∑ j : Fin k, fraction j * fraction (residuePerm h k hk hC j)) - ((k : ℚ) - 1) / 4 := by
  let e := residuePerm h k hk hC
  let f (j : Fin k) := fraction j
  let S (j : Fin k) := sawtooth (f j) * sawtooth (f (e j))
  have hR : dedekindSum (h : ℤ) k = ∑ j : Fin k, S j := by
    unfold dedekindSum
    apply Finset.sum_congr rfl
    intro j _
    simp only [Int.cast_natCast]
    rw [sawtooth_mul_eq_residue h k hk hC]
    rfl
  classical
  let z : Fin k := ⟨0, hk⟩
  have hPoint (j : Fin k) : S j =
      f j * f (e j) - f j / 2 - f (e j) / 2 + 1 / 4 - (if j = z then 1 / 4 else 0) := by
    by_cases hj : j = z
    · subst j
      simp [S, f, fraction, e, z, residuePerm_val, sawtooth]
    · have hjv : j.val ≠ 0 := fun he => hj (Fin.ext he)
      have hk' : (e j).val ≠ 0 := residuePerm_ne_zero h k hk hC hjv
      simp only [S, f, fraction, sawtooth_fin_ne_zero hk j hjv, sawtooth_fin_ne_zero hk (e j) hk',
        if_neg hj, sub_zero]
      ring
  have hFE : ∑ j : Fin k, f (e j) = ∑ j : Fin k, f j :=
    Fintype.sum_equiv e _ _ (fun _ => rfl)
  have hf : ∑ j : Fin k, f j = ((k : ℚ) - 1) / 2 := sum_fraction hk
  rw [hR]
  simp_rw [hPoint]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_div, hFE, hf,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  change (∑ j : Fin k, fraction j * fraction (e j)) - _ - _ + _ - _ = _
  ring

end
end ManuscriptAudit.Paper8DedekindResidueMoments

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8DedekindResidueMoments.dedekindSum_eq_fraction_product
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
