import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-! The two prescribed projective charts already suffice over any valued
fraction field. This is the coordinate calculation used in an extension
across a valuation ring. -/

namespace ManuscriptAudit.NodalValuationCoordinates

section

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
  (v : Valuation K Γ) {x y : K}

private theorem x_lt_y_if_x_large (h : y ^ 2 = x ^ 2 * (x + 1)) (hx : 1 < v x) :
    v x < v y := by
  have hplus : v (x + 1) = v x :=
    v.map_add_eq_of_lt_left (by simpa only [map_one] using hx)
  have hv : v y ^ 2 = v x ^ 2 * v x := by
    simpa only [map_pow, map_mul, hplus] using congrArg v h
  have hlt : v x ^ 2 < v y ^ 2 := by
    rw [hv]
    have hp : 0 < v x ^ 2 := pow_pos (zero_lt_one.trans hx) 2
    simpa only [mul_one] using mul_lt_mul_of_pos_left hx hp
  by_contra hnot
  have hle : v y ≤ v x := le_of_not_gt hnot
  have hh : v y ^ 2 ≤ v x ^ 2 := by gcongr
  exact (not_le_of_gt hlt) hh

/-- If the Z chart coordinates fail to be integral, the Y chart
coordinates X/Y and Z/Y are integral. -/
theorem z_or_y_integral (h : y ^ 2 = x ^ 2 * (x + 1)) :
    (v x ≤ 1 ∧ v y ≤ 1) ∨ (y ≠ 0 ∧ v (x / y) ≤ 1 ∧ v y⁻¹ ≤ 1) := by
  by_cases hy : v y ≤ 1
  · left
    refine ⟨?_, hy⟩
    by_contra hx
    have hxy := x_lt_y_if_x_large v h (lt_of_not_ge hx)
    exact hx (hxy.le.trans hy)
  · right
    have hy' : 1 < v y := lt_of_not_ge hy
    have hny : y ≠ 0 := by
      intro he
      rw [he, map_zero] at hy'
      exact (not_lt_of_ge zero_le_one) hy'
    have hxy : v x ≤ v y := by
      by_cases hx : v x ≤ 1
      · exact hx.trans hy'.le
      · exact (x_lt_y_if_x_large v h (lt_of_not_ge hx)).le
    refine ⟨hny, ?_, (v.one_le_val_iff hny).mp hy'.le⟩
    rw [v.map_div]
    exact (div_le_one₀ (zero_lt_one.trans hy')).mpr hxy

end

/-- The normalized coordinates satisfy the actual printed affine equation in the Y chart. -/
theorem y_chart_equation {K : Type*} [Field K] {x y : K}
    (h : y ^ 2 = x ^ 2 * (x + 1)) (hy : y ≠ 0) :
    y⁻¹ = (x / y) ^ 2 * (x / y + y⁻¹) := by
  calc
    y⁻¹ = y ^ 2 * (y⁻¹) ^ 3 := by field_simp [hy]
    _ = x ^ 2 * (x + 1) * (y⁻¹) ^ 3 := by rw [h]
    _ = (x / y) ^ 2 * (x / y + y⁻¹) := by rw [div_eq_mul_inv]; ring


/-- A point in the field's Z chart has coordinates over the valuation
ring in at least one of the model's two actual charts. -/
theorem valuationRing_coordinates (V K : Type*) [CommRing V] [IsDomain V] [ValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] {x y : K}
    (h : y ^ 2 = x ^ 2 * (x + 1)) :
    (∃ a b : V, algebraMap V K a = x ∧ algebraMap V K b = y ∧
      b ^ 2 = a ^ 2 * (a + 1)) ∨
    (y ≠ 0 ∧ ∃ a b : V, algebraMap V K a = x / y ∧ algebraMap V K b = y⁻¹ ∧
      b = a ^ 2 * (a + b)) := by
  let v := ValuationRing.valuation V K
  rcases z_or_y_integral v h with ⟨ha, hb⟩ | ⟨hy, ha, hb⟩
  · left
    obtain ⟨a, hA⟩ := (ValuationRing.mem_integer_iff V K x).mp ha
    obtain ⟨b, hB⟩ := (ValuationRing.mem_integer_iff V K y).mp hb
    refine ⟨a, b, hA, hB, (IsFractionRing.injective V K) ?_⟩
    simpa only [map_pow, map_mul, map_add, map_one, hA, hB] using h
  · right
    obtain ⟨a, hA⟩ := (ValuationRing.mem_integer_iff V K (x / y)).mp ha
    obtain ⟨b, hB⟩ := (ValuationRing.mem_integer_iff V K y⁻¹).mp hb
    refine ⟨hy, a, b, hA, hB, (IsFractionRing.injective V K) ?_⟩
    simpa only [map_pow, map_mul, map_add, hA, hB] using y_chart_equation h hy

end ManuscriptAudit.NodalValuationCoordinates

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalValuationCoordinates.z_or_y_integral,
      ``ManuscriptAudit.NodalValuationCoordinates.y_chart_equation,
      ``ManuscriptAudit.NodalValuationCoordinates.valuationRing_coordinates] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
