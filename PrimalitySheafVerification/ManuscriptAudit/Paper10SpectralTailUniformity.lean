import Lean.Util.CollectAxioms
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Pointwise rapid decay and a unit-window density bound do not imply the uniform cutoff on p. 501. -/

namespace ManuscriptAudit.Paper10SpectralTailUniformity

open Filter
open scoped Topology ContDiff

noncomputable section

def cutoff (T : ℝ) : ℝ :=
  T + (Real.log T)^2

def center (T : ℝ) : ℕ :=
  ⌈cutoff T⌉₊

/-- A smooth unit bump with compact support around one spectral point in the tail. -/
def weight (T : ℝ) : ContDiffBump (center T : ℝ) :=
  ⟨1/2, 1, by norm_num, by norm_num⟩

theorem weight_smooth (T : ℝ) : ContDiff ℝ ∞ (weight T : ℝ → ℝ) :=
  (weight T).contDiff

theorem weight_eventually_zero (T : ℝ) :
    ∀ᶠ t : ℝ in atTop, weight T t = 0 := by
  apply eventually_atTop.mpr
  refine ⟨(center T : ℝ) + 1, fun t ht => ?_⟩
  apply (weight T).zero_of_le_dist
  change (1 : ℝ) ≤ dist t (center T)
  rw [Real.dist_eq, abs_of_nonneg (by linarith : 0 ≤ t - (center T : ℝ))]
  linarith

theorem unit_windows_have_at_most_two (u : ℝ) :
    ∃ s : Finset ℕ, s.card ≤ 2 ∧ ∀ j : ℕ, j ∈ s ↔ u ≤ (j : ℝ) ∧ (j : ℝ) ≤ u + 1 := by
  classical
  let m : ℕ := ⌈u⌉₊
  let s : Finset ℕ := {m, m+1}
  let P (j : ℕ) : Prop := u ≤ (j : ℝ) ∧ (j : ℝ) ≤ u + 1
  have hm : u ≤ (m : ℝ) := Nat.le_ceil _
  have hcard : s.card = 2 := by
    have hne : m ∉ ({m+1} : Finset ℕ) := by simp
    rw [s, Finset.card_insert_of_notMem hne, Finset.card_singleton]
  refine ⟨s.filter P, (Finset.card_filter_le _ _).trans hcard.le, fun j => ?_⟩
  rw [Finset.mem_filter]
  refine ⟨And.right, fun hj => ⟨?_, hj⟩⟩
  have hjl : m ≤ j := Nat.ceil_le.mpr hj.1
  have hjR : (j : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_add, Nat.cast_one]
    linarith only [hj.2, hm]
  have hjr : j ≤ m+1 := by exact_mod_cast hjR
  have he : j = m ∨ j = m+1 := by omega
  simpa only [s, Finset.mem_insert, Finset.mem_singleton] using he

def tailTerm (T : ℝ) (j : ℕ) : ℝ :=
  if cutoff T ≤ (j : ℝ) then |weight T (j : ℝ)| else 0

theorem tailTerm_eq_single (T : ℝ) (j : ℕ) :
    tailTerm T j = if j = center T then 1 else 0 := by
  by_cases hj : j = center T
  · subst j
    rw [tailTerm, if_pos (Nat.le_ceil _), if_pos rfl]
    have hcenter : weight T (center T : ℝ) = 1 :=
      (weight T).one_of_mem_closedBall (Metric.mem_closedBall_self (weight T).rIn_pos.le)
    rw [hcenter, abs_one]
  · rw [if_neg hj]
    have hd : 1 ≤ dist (j : ℝ) (center T : ℝ) := by
      rw [Real.dist_eq]
      rcases lt_or_gt_of_ne hj with h | h
      · have hN : j+1 ≤ center T := h
        have hR : (j : ℝ)+1 ≤ (center T : ℝ) := by exact_mod_cast hN
        rw [abs_of_nonpos (by linarith : (j : ℝ) - (center T : ℝ) ≤ 0)]
        linarith
      · have hN : center T + 1 ≤ j := h
        have hR : (center T : ℝ)+1 ≤ (j : ℝ) := by exact_mod_cast hN
        rw [abs_of_nonneg (by linarith : 0 ≤ (j : ℝ) - (center T : ℝ))]
        linarith
    have hz : weight T (j : ℝ) = 0 := (weight T).zero_of_le_dist hd
    simp [tailTerm, hz]

theorem exact_tail_mass (T : ℝ) : (∑' j : ℕ, tailTerm T j) = 1 := by
  simp_rw [tailTerm_eq_single]
  exact tsum_eq_single (center T) (fun _ hj => if_neg hj) |>.trans (if_pos rfl)

theorem no_uniform_decay_at_first_power :
    ¬ ∃ C : ℝ, ∀ T : ℝ, 1 ≤ T → (∑' j : ℕ, tailTerm T j) ≤ C / T := by
  rintro ⟨C, h⟩
  let T := |C| + 2
  have hT : 1 ≤ T := by dsimp only [T]; linarith [abs_nonneg C]
  have hh := h T hT
  rw [exact_tail_mass] at hh
  have hTC := (le_div_iff₀ (show 0 < T by linarith)).mp hh
  dsimp only [T] at hTC
  linarith [le_abs_self C]

end
end ManuscriptAudit.Paper10SpectralTailUniformity

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper10SpectralTailUniformity.weight_smooth,
      ``ManuscriptAudit.Paper10SpectralTailUniformity.weight_eventually_zero,
      ``ManuscriptAudit.Paper10SpectralTailUniformity.unit_windows_have_at_most_two,
      ``ManuscriptAudit.Paper10SpectralTailUniformity.tailTerm_eq_single,
      ``ManuscriptAudit.Paper10SpectralTailUniformity.exact_tail_mass,
      ``ManuscriptAudit.Paper10SpectralTailUniformity.no_uniform_decay_at_first_power] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
