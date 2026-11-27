import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Nat.Defs

/-! Two distinct nonzero order-two images force independence of the lifted vectors. -/

namespace ManuscriptAudit.TwoPowerTorsionIndependent

variable {G : Type*} [AddCommGroup G]

private theorem nsmul_mod_of_annihilation (t k : ℕ) (x : G) (h : k • x = 0) :
    t • x = (t % k) • x := by
  calc
    _ = (t % k + k * (t / k)) • x := congrArg (fun m : ℕ => m • x) (Nat.mod_add_div t k).symm
    _ = _ := by rw [add_nsmul, mul_nsmul, h, nsmul_zero, add_zero]

private theorem neg_eq_self_of_two_nsmul {x : G} (h : (2 : ℕ) • x = 0) : -x = x := by
  calc
    _ = -x + (x + x) := by rw [← two_nsmul, h, add_zero]
    _ = _ := by rw [← add_assoc, neg_add_cancel, zero_add]

private theorem even_coefficients {X Y : G} (hX : (2 : ℕ) • X = 0) (hY : (2 : ℕ) • Y = 0)
    (hX₀ : X ≠ 0) (hY₀ : Y ≠ 0) (hXY : X ≠ Y) (a b : ℕ)
    (h : a • X + b • Y = 0) : a % 2 = 0 ∧ b % 2 = 0 := by
  rw [nsmul_mod_of_annihilation a 2 X hX, nsmul_mod_of_annihilation b 2 Y hY] at h
  rcases (show a % 2 = 0 ∨ a % 2 = 1 by omega) with ha | ha
  · rcases (show b % 2 = 0 ∨ b % 2 = 1 by omega) with hb | hb
    · exact ⟨ha, hb⟩
    · exact (hY₀ (by simpa only [ha, hb, zero_nsmul, one_nsmul, zero_add] using h)).elim
  · rcases (show b % 2 = 0 ∨ b % 2 = 1 by omega) with hb | hb
    · exact (hX₀ (by simpa only [ha, hb, zero_nsmul, one_nsmul, add_zero] using h)).elim
    · have he : X + Y = 0 := by simpa only [ha, hb, one_nsmul] using h
      exact (hXY ((eq_neg_of_add_eq_zero_left he).trans (neg_eq_self_of_two_nsmul hY))).elim

private theorem nsmul_commute (a b : ℕ) (x : G) : a • (b • x) = b • (a • x) := by
  rw [← mul_nsmul', mul_nsmul]

/-- A relation in the least nonnegative coefficients of two lifted vectors is trivial. -/
theorem nsmul_relation_unique (n : ℕ) (x y : G)
    (hx : (2 ^ (n + 1) : ℕ) • x = 0) (hy : (2 ^ (n + 1) : ℕ) • y = 0)
    (hX₀ : (2 ^ n : ℕ) • x ≠ 0) (hY₀ : (2 ^ n : ℕ) • y ≠ 0)
    (hXY : (2 ^ n : ℕ) • x ≠ (2 ^ n : ℕ) • y) (a b : ℕ)
    (ha : a < 2 ^ (n + 1)) (hb : b < 2 ^ (n + 1))
    (hrel : a • x + b • y = 0) : a = 0 ∧ b = 0 := by
  induction n generalizing x y a b with
  | zero =>
    simp only [pow_zero, pow_one, one_nsmul] at hx hy hX₀ hY₀ hXY ha hb
    obtain ⟨hA, hB⟩ := even_coefficients hx hy hX₀ hY₀ hXY a b hrel
    omega
  | succ n ih =>
    let X := (2 ^ (n + 1) : ℕ) • x
    let Y := (2 ^ (n + 1) : ℕ) • y
    have hX : (2 : ℕ) • X = 0 := by
      change (2 : ℕ) • ((2 ^ (n + 1) : ℕ) • x) = 0
      rw [← mul_nsmul, ← pow_succ]
      exact hx
    have hY : (2 : ℕ) • Y = 0 := by
      change (2 : ℕ) • ((2 ^ (n + 1) : ℕ) • y) = 0
      rw [← mul_nsmul, ← pow_succ]
      exact hy
    have hr : a • X + b • Y = 0 := by
      have he := congrArg (fun z : G => (2 ^ (n + 1) : ℕ) • z) hrel
      change (2 ^ (n + 1) : ℕ) • (a • x + b • y) = (2 ^ (n + 1) : ℕ) • 0 at he
      rw [nsmul_add, nsmul_commute _ a x, nsmul_commute _ b y, nsmul_zero] at he
      exact he
    obtain ⟨haEven, hbEven⟩ := even_coefficients hX hY hX₀ hY₀ hXY a b hr
    have ha₂ : a = a / 2 * 2 := by omega
    have hb₂ : b = b / 2 * 2 := by omega
    have hrel₂ : (a / 2) • ((2 : ℕ) • x) + (b / 2) • ((2 : ℕ) • y) = 0 := by
      rw [← mul_nsmul', ← mul_nsmul', ← ha₂, ← hb₂]
      exact hrel
    have haSmall : a / 2 < 2 ^ (n + 1) := by
      rw [pow_succ (2 : ℕ) (n + 1)] at ha
      omega
    have hbSmall : b / 2 < 2 ^ (n + 1) := by
      rw [pow_succ (2 : ℕ) (n + 1)] at hb
      omega
    have hx₂ : (2 ^ (n + 1) : ℕ) • ((2 : ℕ) • x) = 0 := by
      rw [← mul_nsmul', ← pow_succ]
      exact hx
    have hy₂ : (2 ^ (n + 1) : ℕ) • ((2 : ℕ) • y) = 0 := by
      rw [← mul_nsmul', ← pow_succ]
      exact hy
    have hX₂ : (2 ^ n : ℕ) • ((2 : ℕ) • x) ≠ 0 := by
      rw [← mul_nsmul', ← pow_succ]
      exact hX₀
    have hY₂ : (2 ^ n : ℕ) • ((2 : ℕ) • y) ≠ 0 := by
      rw [← mul_nsmul', ← pow_succ]
      exact hY₀
    have hXY₂ : (2 ^ n : ℕ) • ((2 : ℕ) • x) ≠ (2 ^ n : ℕ) • ((2 : ℕ) • y) := by
      simp only [← mul_nsmul', ← pow_succ]
      exact hXY
    have ⟨ha₀, hb₀⟩ := ih ((2 : ℕ) • x) ((2 : ℕ) • y) hx₂ hy₂ hX₂ hY₂ hXY₂
      (a / 2) (b / 2) haSmall hbSmall hrel₂
    omega

end ManuscriptAudit.TwoPowerTorsionIndependent

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.TwoPowerTorsionIndependent.nsmul_relation_unique
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"

