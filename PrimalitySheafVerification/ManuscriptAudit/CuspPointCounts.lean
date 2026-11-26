import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Data.Fintype.Option
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Logic.Equiv.Option
import Mathlib.Tactic.Ring

/-!
# Rational points of the affine cusp and its puncture

The actual plane equation y² = x³ has parameter t with x = t²,
y = t³ over every field. Over finite fields the cusp has q points
and removing its rational origin gives q − 1 points. This provides
a point-count check of the signed arithmetic difference in all extensions.
-/

namespace ManuscriptAudit.CuspPointCounts

noncomputable section

variable (K : Type*) [Field K]

/-- The rational points given by the actual affine cusp equation. -/
abbrev curvePoints := {xy : K × K // xy.2 ^ 2 = xy.1 ^ 3}

/-- Removing its origin is equivalent to requiring x to be nonzero. -/
abbrev puncturedPoints := {z : curvePoints K // z.val.1 ≠ 0}

private def fromParameter (t : K) : curvePoints K :=
  ⟨(t ^ 2, t ^ 3), by ring⟩

private def toParameter (z : curvePoints K) : K := by
  classical
  exact if z.val.1 = 0 then 0 else z.val.2 / z.val.1

/-- The normalization parameter gives a bijection on rational points in every characteristic. -/
def parameterEquiv : K ≃ curvePoints K where
  toFun := fromParameter K
  invFun := toParameter K
  left_inv t := by
    classical
    by_cases ht : t = 0
    · simp [ht, fromParameter, toParameter]
    · change (if t ^ 2 = 0 then 0 else t ^ 3 / t ^ 2) = t
      rw [if_neg (pow_ne_zero 2 ht)]
      exact (div_eq_iff (pow_ne_zero 2 ht)).2 (by ring)
  right_inv z := by
    classical
    rcases z with ⟨⟨x, y⟩, hxy⟩
    change y ^ 2 = x ^ 3 at hxy
    apply Subtype.ext
    change ((if x = 0 then 0 else y / x) ^ 2,
      (if x = 0 then 0 else y / x) ^ 3) = (x, y)
    by_cases hx : x = 0
    · have hy0 : y * y = 0 := by simpa [hx, pow_two] using hxy
      have hy : y = 0 := (mul_eq_zero.mp hy0).elim id id
      simp [hx, hy]
    · rw [if_neg hx]
      have hSq : (y / x) ^ 2 = x := by
        rw [div_pow, hxy, div_eq_iff (pow_ne_zero 2 hx)]
        ring
      have hCube : (y / x) ^ 3 = y := by
        rw [pow_succ, hSq, mul_comm, div_mul_cancel₀ _ hx]
      exact Prod.ext hSq hCube

/-- The punctured cusp is parametrized by exactly the nonzero field elements. -/
def punctureEquiv : {t : K // t ≠ 0} ≃ puncturedPoints K where
  toFun t := ⟨parameterEquiv K t.val, pow_ne_zero 2 t.property⟩
  invFun z := by
    let t := (parameterEquiv K).symm z.val
    refine ⟨t, ?_⟩
    intro ht
    have he := congrArg (fun p : curvePoints K => p.val.1)
      ((parameterEquiv K).apply_symm_apply z.val)
    change t ^ 2 = z.val.val.1 at he
    exact z.property (by simpa [ht] using he.symm)
  left_inv t := Subtype.ext ((parameterEquiv K).symm_apply_apply t.val)
  right_inv z := Subtype.ext ((parameterEquiv K).apply_symm_apply z.val)

theorem curve_card : Nat.card (curvePoints K) = Nat.card K :=
  Nat.card_congr (parameterEquiv K).symm

theorem punctured_add_one_card [Finite K] :
    Nat.card (puncturedPoints K) + 1 = Nat.card (curvePoints K) := by
  classical
  letI : Fintype (puncturedPoints K) := Fintype.ofFinite _
  letI : Fintype (curvePoints K) := Fintype.ofFinite _
  let e : Option (puncturedPoints K) ≃ curvePoints K :=
    (Equiv.optionCongr (punctureEquiv K).symm).trans
      ((Equiv.optionSubtypeNe (0 : K)).trans (parameterEquiv K))
  have h := Fintype.card_congr e
  rw [Fintype.card_option] at h
  simpa only [Nat.card_eq_fintype_card] using h

theorem prime_power_point_counts (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) :
    Nat.card (curvePoints (GaloisField p n)) = p ^ n ∧
    Nat.card (puncturedPoints (GaloisField p n)) = p ^ n - 1 := by
  have h := (curve_card (GaloisField p n)).trans (GaloisField.card p (n := n) hn)
  have hp := punctured_add_one_card (GaloisField p n)
  exact ⟨h, by omega⟩

end

end ManuscriptAudit.CuspPointCounts

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CuspPointCounts.parameterEquiv,
      ``ManuscriptAudit.CuspPointCounts.punctureEquiv,
      ``ManuscriptAudit.CuspPointCounts.curve_card,
      ``ManuscriptAudit.CuspPointCounts.punctured_add_one_card,
      ``ManuscriptAudit.CuspPointCounts.prime_power_point_counts] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
