import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import PrimalitySheafVerification.ManuscriptAudit.Paper8ContourResidueWeights

/-! Distribution and periodicity of the literal rational sawtooth in the p. 335 contour. -/

namespace ManuscriptAudit.Paper8SawtoothDistribution

open Paper8ContourResidueWeights

theorem sawtooth_int_translate (x : ℚ) (z : ℤ) :
    sawtooth (x+(z : ℚ)) = sawtooth x := by
  unfold sawtooth
  rw [Int.floor_add_intCast, Int.cast_add]
  have h : x + (z : ℚ) = (⌊x⌋ : ℚ) + (z : ℚ) ↔ x = (⌊x⌋ : ℚ) :=
    ⟨add_right_cancel, fun he => congrArg (fun y : ℚ => y+z) he⟩
  by_cases he : x = (⌊x⌋ : ℚ)
  · rw [if_pos (h.mpr he), if_pos he]
  · rw [if_neg (fun e => he (h.mp e)), if_neg he]
    ring

theorem sawtooth_on_unit {x : ℚ} (hx : 0 ≤ x) (hx' : x < 1) :
    sawtooth x = x - 1/2 + if x = 0 then 1/2 else 0 := by
  have hf : ⌊x⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨hx,hx'⟩
  rw [sawtooth, hf, Int.cast_zero, sub_zero]
  by_cases h : x = 0 <;> simp [h]

private theorem twice_sum_fin_vals (g : ℕ) :
    2 * (∑ j : Fin g, (j.val : ℚ)) = (g : ℚ) * ((g : ℚ)-1) := by
  induction g with
  | zero => simp
  | succ g ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_succ]
    nlinarith only [ih]

private theorem sum_linear_terms (g : ℕ) (hg : 0 < g) (x : ℚ) :
    (∑ j : Fin g, ((x+(j.val : ℚ))/(g : ℚ) - 1/2)) = x - 1/2 := by
  have hgq : (0 : ℚ) < (g : ℚ) := by exact_mod_cast hg
  rw [Finset.sum_sub_distrib]
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hgq.ne']
  nlinarith only [twice_sum_fin_vals g]

private theorem sum_zero_correction (g : ℕ) (hg : 0 < g) (x : ℚ) :
    (∑ j : Fin g, if x = 0 ∧ j.val = 0 then (1/2 : ℚ) else 0) =
      if x = 0 then 1/2 else 0 := by
  by_cases hx : x = 0
  · letI : NeZero g := ⟨Nat.ne_of_gt hg⟩
    simp only [hx, true_and, if_pos rfl]
    rw [Finset.sum_eq_single (0 : Fin g)]
    · simp
    · intro b _ hb
      apply if_neg
      intro h
      exact hb (Fin.ext (by simpa only [Fin.val_zero] using h))
    · simp
  · simp [hx]

theorem distribution (g : ℕ) (hg : 0 < g) {x : ℚ} (hx : 0 ≤ x) (hx' : x < 1) :
    (∑ j : Fin g, sawtooth ((x+(j.val : ℚ))/(g : ℚ))) = sawtooth x := by
  have hgq : (0 : ℚ) < (g : ℚ) := by exact_mod_cast hg
  have hw (j : Fin g) :
      sawtooth ((x+(j.val : ℚ))/(g : ℚ)) =
        (x+(j.val : ℚ))/(g : ℚ) - 1/2 + if x = 0 ∧ j.val = 0 then 1/2 else 0 := by
    have hj0 : (0 : ℚ) ≤ (j.val : ℚ) := Nat.cast_nonneg _
    have hj : (j.val : ℚ)+1 ≤ (g : ℚ) := by
      exact_mod_cast (show j.val+1 ≤ g from j.isLt)
    have h0 : 0 ≤ (x+(j.val : ℚ))/(g : ℚ) := div_nonneg (add_nonneg hx hj0) hgq.le
    have h1 : (x+(j.val : ℚ))/(g : ℚ) < 1 := (div_lt_one₀ hgq).mpr (by linarith)
    rw [sawtooth_on_unit h0 h1]
    have hz : (x+(j.val : ℚ))/(g : ℚ) = 0 ↔ x = 0 ∧ j.val = 0 := by
      constructor
      · intro he
        have hn := (div_eq_zero_iff.mp he).resolve_right hgq.ne'
        have hx0 : x = 0 := by linarith
        have hjz : (j.val : ℚ) = 0 := by linarith
        exact ⟨hx0, by exact_mod_cast hjz⟩
      · rintro ⟨he, hjz⟩
        simp [he, hjz]
    by_cases hZero : x = 0 ∧ j.val = 0
    · rw [if_pos (hz.mpr hZero), if_pos hZero]
    · rw [if_neg (fun he => hZero (hz.mp he)), if_neg hZero]
  simp_rw [hw]
  rw [Finset.sum_add_distrib, sum_linear_terms g hg x, sum_zero_correction g hg x,
    sawtooth_on_unit hx hx']

end ManuscriptAudit.Paper8SawtoothDistribution

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8SawtoothDistribution.sawtooth_int_translate,
      ``ManuscriptAudit.Paper8SawtoothDistribution.sawtooth_on_unit,
      ``ManuscriptAudit.Paper8SawtoothDistribution.distribution] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
