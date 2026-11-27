import Lean.Util.CollectAxioms
import Mathlib.Tactic.LinearCombination
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryThirteenSecant

/-! The coordinate equation for the kernel of 3−ρ² in characteristic thirteen. -/

namespace ManuscriptAudit.Paper5OrdinaryThirteenTorsionAlgebra

open CubicTriplingCoordinates Paper5OrdinaryThirteenAlgebra Paper5OrdinaryThirteenSecant

noncomputable section

variable {K : Type*} [Field K] [CharP K 13]

def torsionQuadratic (t : K) : K := 2 * t ^ 2 + 10 * t + 9

theorem torsionQuadratic_equiv_square (t : K) :
    torsionQuadratic t = 0 ↔ (4 * t + 10) ^ 2 = 2 := by
  have h : (4 * t + 10) ^ 2 - 2 = 8 * torsionQuadratic t := by
    unfold torsionQuadratic
    linear_combination (2 : K) * (thirteen_zero (K := K))
  constructor
  · intro ht
    apply sub_eq_zero.mp
    rw [h, ht, mul_zero]
  · intro ht
    have hz : 8 * torsionQuadratic t = 0 := by rw [← h, ht, sub_self]
    exact (mul_eq_zero.mp hz).resolve_left (numeral_ne_zero 8 (by decide))

theorem torsionQuadratic_nonzero_values {t : K} (h : torsionQuadratic t = 0) :
    t ≠ 0 ∧ t + 1 ≠ 0 ∧ t + 4 ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro ht
    apply numeral_ne_zero (K := K) 9 (by decide)
    simpa [torsionQuadratic, ht] using h
  · intro ht
    have h' : t = -1 := eq_neg_iff_add_eq_zero.mpr ht
    apply (one_ne_zero : (1 : K) ≠ 0)
    rw [h'] at h
    unfold torsionQuadratic at h
    linear_combination h
  · intro ht
    have h' : t = -4 := eq_neg_iff_add_eq_zero.mpr ht
    apply (one_ne_zero : (1 : K) ≠ 0)
    rw [h'] at h
    unfold torsionQuadratic at h
    linear_combination h

private theorem abscissa_condition (t : K) :
    9 * tripleDen t - tripleNum t = (t + 3) * torsionQuadratic t := by
  unfold tripleDen tripleNum torsionQuadratic
  linear_combination (6 * t ^ 3 + 56 * t ^ 2 + 93 * t - 7) * (thirteen_zero (K := K))

private theorem slope_condition (t : K) :
    tripleSlopeNum t - 18 * (t + 1) * (t + 4) = torsionQuadratic t := by
  unfold tripleSlopeNum torsionQuadratic
  linear_combination (-(t ^ 2 + 8 * t + 5)) * (thirteen_zero (K := K))

theorem tripleX_of_quadratic {x : K} (h : torsionQuadratic (x ^ 3) = 0) :
    tripleX x = 9 * x := by
  obtain ⟨ht, -, hg⟩ := torsionQuadratic_nonzero_values h
  have hx : x ≠ 0 := fun hx => ht (by simp [hx])
  have hd := tripleDen_ne_zero hx hg
  have hn : tripleNum (x ^ 3) = 9 * tripleDen (x ^ 3) := by
    symm
    apply sub_eq_zero.mp
    rw [abscissa_condition, h, mul_zero]
  have hFrac : tripleNum (x ^ 3) / tripleDen (x ^ 3) = 9 := (div_eq_iff hd).mpr hn
  rw [tripleX, hFrac, mul_comm]

theorem tripleY_eq_iff_quadratic {x y : K} (hx : x ≠ 0) (hy : y ≠ 0)
    (hg : x ^ 3 + 4 ≠ 0) (he : y ^ 2 = x ^ 3 + 1) (hX : tripleX x = 9 * x) :
    tripleY x y = y ↔ torsionQuadratic (x ^ 3) = 0 := by
  let t := x ^ 3
  let b := tripleSlopeNum t / (6 * (t + 1) * (t + 4))
  have h₆ : (6 : K) ≠ 0 := numeral_ne_zero 6 (by decide)
  have h₈ : (8 : K) ≠ 0 := numeral_ne_zero 8 (by decide)
  have hs : t + 1 ≠ 0 := he ▸ pow_ne_zero 2 hy
  have hd : 6 * (t + 1) * (t + 4) ≠ 0 := mul_ne_zero (mul_ne_zero h₆ hs) hg
  have hDiff : tripleY x y - y = (-8 * y) * (b - 3) := by
    unfold tripleY
    rw [hX, thirdSlope_normalized hx hy hg he]
    change ((y / x) * b) * (x - 9 * x) - y - y = _
    calc
      _ = ((y / x) * x) * (-8 * b) - y - y := by ring
      _ = _ := by
        rw [div_mul_cancel₀ _ hx]
        linear_combination (-2 * y) * (thirteen_zero (K := K))
  have hB : b = 3 ↔ torsionQuadratic t = 0 := by
    change tripleSlopeNum t / (6 * (t + 1) * (t + 4)) = 3 ↔ _
    rw [div_eq_iff hd]
    constructor
    · intro hb
      rw [← slope_condition t, hb]
      ring
    · intro hb
      have ht := (slope_condition t).trans hb
      have heq := sub_eq_zero.mp ht
      rw [heq]
      ring
  constructor
  · intro hy'
    have hz : (-8 * y) * (b - 3) = 0 := by rw [← hDiff, hy', sub_self]
    have hb' := (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (neg_ne_zero.mpr h₈) hy)
    exact hB.mp (sub_eq_zero.mp hb')
  · intro hQ
    apply sub_eq_zero.mp
    rw [hDiff, hB.mpr hQ, sub_self, mul_zero]

end
end ManuscriptAudit.Paper5OrdinaryThirteenTorsionAlgebra

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5OrdinaryThirteenTorsionAlgebra.torsionQuadratic_equiv_square,
      ``ManuscriptAudit.Paper5OrdinaryThirteenTorsionAlgebra.torsionQuadratic_nonzero_values,
      ``ManuscriptAudit.Paper5OrdinaryThirteenTorsionAlgebra.tripleX_of_quadratic,
      ``ManuscriptAudit.Paper5OrdinaryThirteenTorsionAlgebra.tripleY_eq_iff_quadratic] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
