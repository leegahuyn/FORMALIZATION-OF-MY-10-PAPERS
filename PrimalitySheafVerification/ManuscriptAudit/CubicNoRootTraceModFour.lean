import Lean.Util.CollectAxioms
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.FiniteFieldPointCount

/-! The parity of the quadratic-character product controls the signed count modulo four. -/

namespace ManuscriptAudit.CubicNoRootTraceModFour

open FiniteFieldPointCount

private theorem insert_rule :
    ∀ c u v : ZMod 4, (u = 1 ∨ u = -1) → (v = 1 ∨ v = -1) →
      (u * v = 1 ∨ u * v = -1) ∧
      u + (c + v - 1) = (c + 1) + u * v - 1 := by decide

private theorem sum_prod_signs {α : Type*} (s : Finset α) (f : α → ℤ)
    (hf : ∀ x ∈ s, f x = 1 ∨ f x = -1) :
    let P := ((∏ x ∈ s, f x : ℤ) : ZMod 4)
    (P = 1 ∨ P = -1) ∧
      ((∑ x ∈ s, f x : ℤ) : ZMod 4) = (s.card : ZMod 4) + P - 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have ha' := hf a (Finset.mem_insert_self a s)
      have hs := ih (fun x hx => hf x (Finset.mem_insert_of_mem hx))
      have hu : (f a : ZMod 4) = 1 ∨ (f a : ZMod 4) = -1 := by
        rcases ha' with h | h
        · exact Or.inl (by simp only [h, Int.cast_one])
        · exact Or.inr (by simp only [h, Int.cast_neg, Int.cast_one])
      let c := (s.card : ZMod 4)
      let v := ((∏ x ∈ s, f x : ℤ) : ZMod 4)
      have h := insert_rule c (f a) v hu hs.1
      dsimp only
      rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.card_insert_of_notMem ha,
        Int.cast_mul, Int.cast_add, Nat.cast_add, Nat.cast_one, hs.2]
      exact h

noncomputable section

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- With no roots in the base field of size three modulo four, the native signed projective
point count is the quadratic character of the product of the cubic values, modulo four. -/
theorem signed_trace_eq_quadratic_product {A : K}
    (hchar : ringChar K ≠ 2) (hΔ : (shortCubic (0 : K) A).Δ ≠ 0)
    (hq : (Fintype.card K : ZMod 4) = 3) (hNo : ∀ x : K, x ^ 3 + A ≠ 0) :
    (((Fintype.card K : ℤ) + 1 - (Nat.card (shortCubic (0 : K) A).toProjective.Point : ℤ) : ℤ) :
      ZMod 4) = (quadraticChar K (∏ x : K, (x ^ 3 + A)) : ZMod 4) := by
  have hc := shortCubic_projective_count_int hchar hΔ
  simp only [zero_mul, sub_zero] at hc
  have hs := sum_prod_signs (Finset.univ : Finset K) (fun x => quadraticChar K (x ^ 3 + A))
    (fun x _ => quadraticChar_dichotomy (hNo x))
  have htrace : (Fintype.card K : ℤ) + 1 -
      (Nat.card (shortCubic (0 : K) A).toProjective.Point : ℤ) =
        -(∑ x : K, quadraticChar K (x ^ 3 + A)) := by
    rw [hc]
    ring
  rw [htrace, Int.cast_neg, hs.2, Finset.card_univ, hq, map_prod]
  rcases hs.1 with h | h <;> rw [h] <;> decide

end
end ManuscriptAudit.CubicNoRootTraceModFour

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicNoRootTraceModFour.signed_trace_eq_quadratic_product
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
