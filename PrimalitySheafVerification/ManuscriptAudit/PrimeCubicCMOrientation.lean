import Lean.Util.CollectAxioms
import Mathlib.Tactic.LinearCombination
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Data.ZMod.Basic

/-! The integral trace-and-norm pair has a unique zero reduction at a chosen prime-field cube root. -/

namespace ManuscriptAudit.PrimeCubicCMOrientation

noncomputable section

variable (p : ℕ) [Fact p.Prime]

private theorem quadratic {z : ZMod p} (hz : IsPrimitiveRoot z 3) : z ^ 2 + z + 1 = 0 := by
  have he : (z - 1) * (z ^ 2 + z + 1) = 0 := by
    calc
      _ = z ^ 3 - 1 := by ring
      _ = _ := by rw [hz.pow_eq_one, sub_self]
  exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr (hz.ne_one (by decide)))

private theorem norm_cast_zero {a b : ℤ} (hn : a ^ 2 - a * b + b ^ 2 = (p : ℤ)) :
    (a : ZMod p) ^ 2 - (a : ZMod p) * (b : ZMod p) + (b : ZMod p) ^ 2 = 0 := by
  simpa only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast, ZMod.natCast_self]
    using congrArg (fun x : ℤ => (x : ZMod p)) hn

private theorem second_cast_ne_zero {a b : ℤ} (hn : a ^ 2 - a * b + b ^ 2 = (p : ℤ)) :
    (b : ZMod p) ≠ 0 := by
  intro hb
  have ha₂ : (a : ZMod p) * (a : ZMod p) = 0 := by
    simpa [hb, pow_two] using norm_cast_zero p hn
  have ha := (mul_eq_zero.mp ha₂).elim id id
  obtain ⟨u, ha'⟩ := (CharP.intCast_eq_zero_iff (ZMod p) p a).mp ha
  obtain ⟨v, hb'⟩ := (CharP.intCast_eq_zero_iff (ZMod p) p b).mp hb
  rw [ha', hb'] at hn
  have hp : p.Prime := Fact.out
  have hP : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h : ((p : ℤ) * (u ^ 2 - u * v + v ^ 2)) = 1 := by
    apply mul_left_cancel₀ hP
    calc
      _ = ((p : ℤ) * u) ^ 2 - ((p : ℤ) * u) * ((p : ℤ) * v) + ((p : ℤ) * v) ^ 2 := by ring
      _ = _ := by simpa only [mul_one] using hn
  have hd : (p : ℤ) ∣ (1 : ℤ) := ⟨_, h.symm⟩
  have hd' : p ∣ (1 : ℕ) := Int.natCast_dvd_natCast.mp hd
  exact (not_le_of_gt hp.one_lt) (Nat.le_of_dvd (by decide) hd')

private theorem evaluate_conjugate {z : ZMod p} (hz : IsPrimitiveRoot z 3) (a b : ℤ) :
    ((a - b : ℤ) : ZMod p) + ((-b : ℤ) : ZMod p) * z =
      (a : ZMod p) + (b : ZMod p) * z ^ 2 := by
  push_cast
  linear_combination (-(b : ZMod p)) * quadratic p hz

private theorem norm_factor {a b : ℤ} {z : ZMod p} (hz : IsPrimitiveRoot z 3)
    (hn : a ^ 2 - a * b + b ^ 2 = (p : ℤ)) :
    ((a : ZMod p) + (b : ZMod p) * z) * ((a : ZMod p) + (b : ZMod p) * z ^ 2) = 0 := by
  have hs : z + z ^ 2 = -1 := by linear_combination quadratic p hz
  calc
    _ = (a : ZMod p) ^ 2 + (a : ZMod p) * (b : ZMod p) * (z + z ^ 2) +
        (b : ZMod p) ^ 2 * z ^ 3 := by ring
    _ = 0 := by
      rw [hs, hz.pow_eq_one]
      linear_combination norm_cast_zero p hn

private theorem square_ne_root {z : ZMod p} (hz : IsPrimitiveRoot z 3) : z ≠ z ^ 2 := by
  intro h
  have h0 : z ≠ 0 := by
    intro hz₀
    have hp := hz.pow_eq_one
    simp [hz₀] at hp
  have h1 : z * 1 = z * z := by rw [mul_one, ← pow_two, h]
  exact hz.ne_one (by decide) (mul_left_cancel₀ h0 h1).symm

private theorem not_both_zero {a b : ℤ} {z : ZMod p} (hz : IsPrimitiveRoot z 3)
    (hn : a ^ 2 - a * b + b ^ 2 = (p : ℤ))
    (h₁ : (a : ZMod p) + (b : ZMod p) * z = 0)
    (h₂ : (a : ZMod p) + (b : ZMod p) * z ^ 2 = 0) : False := by
  have hDiff : (b : ZMod p) * (z - z ^ 2) = 0 := by linear_combination h₁ - h₂
  exact (mul_ne_zero (second_cast_ne_zero p hn) (sub_ne_zero.mpr (square_ne_root p hz))) hDiff

/-- Of the integral trace-and-norm pairs, exactly one reduces to zero at the chosen primitive root. -/
theorem exists_unique_zero_reduction {z : ZMod p} (hz : IsPrimitiveRoot z 3) {t : ℤ}
    (h : ∃ a b : ℤ, t = 2 * a - b ∧ a ^ 2 - a * b + b ^ 2 = (p : ℤ)) :
    ∃! ab : ℤ × ℤ, t = 2 * ab.1 - ab.2 ∧ ab.1 ^ 2 - ab.1 * ab.2 + ab.2 ^ 2 = (p : ℤ) ∧
      (ab.1 : ZMod p) + (ab.2 : ZMod p) * z = 0 := by
  have hex : ∃ ab : ℤ × ℤ, t = 2 * ab.1 - ab.2 ∧ ab.1 ^ 2 - ab.1 * ab.2 + ab.2 ^ 2 = (p : ℤ) ∧
      (ab.1 : ZMod p) + (ab.2 : ZMod p) * z = 0 := by
    obtain ⟨a, b, ha, hn⟩ := h
    rcases mul_eq_zero.mp (norm_factor p hz hn) with h₁ | h₂
    · exact ⟨(a, b), ha, hn, h₁⟩
    · refine ⟨(a - b, -b), ?_, ?_, ?_⟩
      · change t = 2 * (a - b) - (-b)
        linear_combination ha
      · change (a - b) ^ 2 - (a - b) * (-b) + (-b) ^ 2 = (p : ℤ)
        linear_combination hn
      · exact (evaluate_conjugate p hz a b).trans h₂
  obtain ⟨⟨a, b⟩, ha, hn, hEval⟩ := hex
  refine ⟨(a, b), ⟨ha, hn, hEval⟩, ?_⟩
  rintro ⟨c, d⟩ ⟨hc, hm, hEval'⟩
  change t = 2 * a - b at ha
  change t = 2 * c - d at hc
  change a ^ 2 - a * b + b ^ 2 = (p : ℤ) at hn
  change c ^ 2 - c * d + d ^ 2 = (p : ℤ) at hm
  change (a : ZMod p) + (b : ZMod p) * z = 0 at hEval
  change (c : ZMod p) + (d : ZMod p) * z = 0 at hEval'
  have hs₁ : (2 * a - b) ^ 2 + 3 * b ^ 2 = 4 * (p : ℤ) := by linear_combination 4 * hn
  have hs₂ : (2 * c - d) ^ 2 + 3 * d ^ 2 = 4 * (p : ℤ) := by linear_combination 4 * hm
  have hs : (2 * a - b) ^ 2 = (2 * c - d) ^ 2 :=
    congrArg (fun v : ℤ => v ^ 2) (ha.symm.trans hc)
  have hmul : (3 : ℤ) * (d ^ 2 - b ^ 2) = 0 := by
    linear_combination hs₂ - hs₁ + hs
  have hsq : d ^ 2 = b ^ 2 :=
    sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left (by decide))
  have hprod : (d - b) * (d + b) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp hprod with he | he
  · have hd : d = b := sub_eq_zero.mp he
    have hC : c = a := by omega
    exact Prod.ext hC hd
  · have hd : d = -b := eq_neg_iff_add_eq_zero.mpr he
    have hC : c = a - b := by omega
    have h₂ : (a : ZMod p) + (b : ZMod p) * z ^ 2 = 0 := by
      rw [hC, hd] at hEval'
      exact (evaluate_conjugate p hz a b).symm.trans hEval'
    exact (not_both_zero p hz hn hEval h₂).elim

end
end ManuscriptAudit.PrimeCubicCMOrientation

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.PrimeCubicCMOrientation.exists_unique_zero_reduction
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
