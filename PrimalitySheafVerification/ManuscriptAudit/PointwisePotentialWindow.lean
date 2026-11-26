import Lean.Util.CollectAxioms
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Pointwise bounded potentials and uniform spectral-window counts

This model uses the eigenvalue multiplicities of a two-dimensional
reference counting law and actual diagonal multiplication of bounded
size at each parameter in a compact real interval. The window at
T=1 has arbitrarily large finite cardinality.
-/

namespace ManuscriptAudit.PointwisePotentialWindow

open Set

noncomputable section

abbrev Index := Σ n : ℕ, Fin (2 * n + 1)

def levelValue (n : ℕ) : ℝ := 5 / 4 + (n : ℝ) * ((n : ℝ) + 1)

def referenceValue (i : Index) : ℝ := levelValue i.1

def potential (n : ℕ) (i : Index) : ℝ :=
  if i.1 = n then -(n : ℝ) * ((n : ℝ) + 1) else 0

def lambda (n : ℕ) (i : Index) : ℝ := referenceValue i + potential n i

def t (n : ℕ) (i : Index) : ℝ := Real.sqrt (lambda n i - 1 / 4)

def parameter (n : ℕ) : ℝ := 1 / 2 + 1 / (4 * ((n : ℝ) + 1))

private theorem levelValue_le_iff {m n : ℕ} : levelValue m ≤ levelValue n ↔ m ≤ n := by
  constructor
  · intro h
    by_contra! hm
    have hmn : (n : ℝ) < m := by exact_mod_cast hm
    have h := mul_lt_mul_of_pos_right hmn (show 0 < (n : ℝ) + 1 by positivity)
    have h' : (m : ℝ) * ((n : ℝ) + 1) ≤ (m : ℝ) * ((m : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg m)
    unfold levelValue at *
    linarith
  · intro h
    have hmn : (m : ℝ) ≤ n := by exact_mod_cast h
    have h := mul_le_mul hmn (by linarith : (m : ℝ) + 1 ≤ (n : ℝ) + 1)
      (by positivity) (Nat.cast_nonneg n)
    unfold levelValue
    linarith

private def cutoffEquiv (N : ℕ) :
    {i : Index // referenceValue i ≤ levelValue N} ≃
      (Σ n : Fin (N + 1), Fin (2 * n.val + 1)) where
  toFun i := ⟨⟨i.val.1, Nat.lt_succ_of_le (levelValue_le_iff.mp i.property)⟩, i.val.2⟩
  invFun i := ⟨⟨i.1.val, i.2⟩, levelValue_le_iff.mpr (Nat.le_of_lt_succ i.1.isLt)⟩
  left_inv _ := by rfl
  right_inv i := by
    obtain ⟨⟨n, hn⟩, r⟩ := i
    rfl

private theorem sum_level_ranks (N : ℕ) :
    (∑ n : Fin (N + 1), (2 * n.val + 1)) = (N + 1) ^ 2 := by
  induction N with
  | zero => decide
  | succ N h =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [h]
    ring

theorem reference_count_at_level (N : ℕ) :
    Nat.card {i : Index // referenceValue i ≤ levelValue N} = (N + 1) ^ 2 := by
  rw [Nat.card_congr (cutoffEquiv N), Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact sum_level_ranks N

theorem parameter_in_compact_interval (n : ℕ) : parameter n ∈ Icc (1 / 2) (3 / 4) := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hd : (4 : ℝ) ≤ 4 * ((n : ℝ) + 1) := by linarith
  have hp : 0 ≤ 1 / (4 * ((n : ℝ) + 1)) := by positivity
  have hq : 1 / (4 * ((n : ℝ) + 1)) ≤ (1 / 4 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) hd
  unfold parameter
  exact ⟨by linarith, by linarith⟩

theorem potential_bounded_at_each_parameter (n : ℕ) (i : Index) :
    |potential n i| ≤ (n : ℝ) * ((n : ℝ) + 1) := by
  have hp : 0 ≤ (n : ℝ) * ((n : ℝ) + 1) := by positivity
  by_cases h : i.1 = n
  · simp [potential, h, abs_of_nonneg hp, neg_mul]
  · simpa only [potential, if_neg h, abs_zero] using hp

private theorem lambda_same_block {n : ℕ} {i : Index} (h : i.1 = n) :
    lambda n i = 5 / 4 := by
  simp only [lambda, referenceValue, levelValue, potential, h, if_pos]
  ring

theorem lambda_ge_threshold (n : ℕ) (i : Index) : 5 / 4 ≤ lambda n i := by
  by_cases h : i.1 = n
  · rw [lambda_same_block h]
  · have h₀ : 0 ≤ (i.1 : ℝ) * ((i.1 : ℝ) + 1) := by positivity
    simpa only [lambda, potential, if_neg h, add_zero, referenceValue, levelValue, le_add_iff_nonneg_right]
      using h₀

theorem actual_real_parameter (n : ℕ) (i : Index) :
    0 ≤ t n i ∧ lambda n i = 1 / 4 + t n i ^ 2 := by
  have h : 0 ≤ lambda n i - 1 / 4 := by linarith [lambda_ge_threshold n i]
  refine ⟨Real.sqrt_nonneg _, ?_⟩
  rw [t, Real.sq_sqrt h]
  ring

abbrev UnitWindow (n : ℕ) := {i : Index // t n i ∈ Icc (1 : ℝ) 2}

private theorem window_index_le (n : ℕ) (i : UnitWindow n) : i.val.1 ≤ max n 1 := by
  by_cases hi : i.val.1 = n
  · rw [hi]; exact le_max_left _ _
  have hT := actual_real_parameter n i.val
  have ht : t n i.val ^ (2 : ℕ) ≤ (2 : ℝ) ^ (2 : ℕ) :=
    pow_le_pow_left₀ hT.1 i.property.2 _
  have hValue := hT.2
  rw [lambda, referenceValue, levelValue, potential, if_neg hi, add_zero] at hValue
  by_contra! hx
  have hn : 2 ≤ i.val.1 := by
    have := le_max_right n 1
    omega
  have hn' : (2 : ℝ) ≤ i.val.1 := by exact_mod_cast hn
  have hProd : (6 : ℝ) ≤ (i.val.1 : ℝ) * ((i.val.1 : ℝ) + 1) := by
    have h := mul_le_mul hn' (show (3 : ℝ) ≤ (i.val.1 : ℝ) + 1 by linarith)
      (by norm_num : (0 : ℝ) ≤ 3) (by positivity)
    linarith
  linarith only [hValue, hProd, ht]

theorem finite_window (n : ℕ) : Finite (UnitWindow n) := by
  let J := Σ m : Fin (max n 1 + 1), Fin (2 * m.val + 1)
  let into (i : UnitWindow n) : J :=
    ⟨⟨i.val.1, Nat.lt_succ_of_le (window_index_le n i)⟩, i.val.2⟩
  let forget (j : J) : Index := ⟨j.1.val, j.2⟩
  apply Finite.of_injective into
  intro i j h
  exact Subtype.ext (congrArg forget h)

theorem window_card_ge_block (n : ℕ) : 2 * n + 1 ≤ Nat.card (UnitWindow n) := by
  letI := finite_window n
  let put (i : Fin (2 * n + 1)) : UnitWindow n :=
    ⟨⟨n, i⟩, by
      change t n ⟨n, i⟩ ∈ Icc (1 : ℝ) 2
      have h : lambda n (⟨n, i⟩ : Index) = 5 / 4 :=
        lambda_same_block (i := ⟨n, i⟩) (n := n) rfl
      rw [t, h]
      norm_num [Set.mem_Icc]⟩
  have hinj : Function.Injective put := by
    intro i j he
    have hk := congrArg (fun v : UnitWindow n => v.val.2.val) he
    exact Fin.ext hk
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective put hinj

theorem no_uniform_window_bound :
    ¬ ∃ C : ℝ, ∀ n : ℕ, parameter n ∈ Icc (1 / 2) (3 / 4) →
      (Nat.card (UnitWindow n) : ℝ) ≤ C * (1 + 1) := by
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * C)
  have hL : (↑(2 * n + 1) : ℝ) ≤ Nat.card (UnitWindow n) := by
    exact_mod_cast window_card_ge_block n
  have hU := hC n (parameter_in_compact_interval n)
  push_cast at hL
  linarith [Nat.cast_nonneg (α := ℝ) n]

end
end ManuscriptAudit.PointwisePotentialWindow

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.PointwisePotentialWindow.parameter_in_compact_interval,
      ``ManuscriptAudit.PointwisePotentialWindow.reference_count_at_level,
      ``ManuscriptAudit.PointwisePotentialWindow.potential_bounded_at_each_parameter,
      ``ManuscriptAudit.PointwisePotentialWindow.actual_real_parameter,
      ``ManuscriptAudit.PointwisePotentialWindow.finite_window,
      ``ManuscriptAudit.PointwisePotentialWindow.window_card_ge_block,
      ``ManuscriptAudit.PointwisePotentialWindow.no_uniform_window_bound] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
