import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-! A nonzero parameter on a local chart with reduced quotient cannot
have ramification exponent larger than one in a local uniformizer. -/

namespace ManuscriptAudit.ReducedFibreRamification

noncomputable section

variable {B : Type*} [CommRing B] [IsLocalRing B]

/-- Reducedness of the actual principal fibre rules out every higher power
of a nonunit as its nonzero parameter, even when the chart is not noetherian. -/
theorem exponent_eq_one (s w : B) (u : Bˣ) (e : ℕ) (he : 0 < e)
    (hs : s ≠ 0) (hw : w ∈ IsLocalRing.maximalIdeal B)
    (h : s = w ^ e * (u : B)) [IsReduced (B ⧸ Ideal.span ({s} : Set B))] :
    e = 1 := by
  by_contra he'
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, e = n + 2 := ⟨e - 2, by omega⟩
  let J := Ideal.span ({s} : Set B)
  let q := Ideal.Quotient.mk J
  have hsJ : s ∈ J := Ideal.subset_span (by simp)
  have hpow : w ^ (n+2) = s * ((u⁻¹ : Bˣ) : B) := by
    rw [h, mul_assoc]
    simp
  have hnil : IsNilpotent (q w) := ⟨n+2, by
    rw [← map_pow, hpow, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr hsJ, zero_mul]⟩
  have hwJ : w ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp (IsReduced.eq_zero _ hnil)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hwJ
  let t : B := w ^ (n+1) * ((u : B) * c)
  have ht : t ∈ IsLocalRing.maximalIdeal B := by
    change w ^ (n+1) * ((u : B) * c) ∈ _
    rw [pow_succ', mul_assoc]
    exact (IsLocalRing.maximalIdeal B).mul_mem_right _ hw
  have htUnit : IsUnit (1 - t) := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits t ht
  have hwt : w = w * t := by
    calc
      _ = s * c := hc
      _ = w ^ (n+2) * ((u : B) * c) := by rw [h, mul_assoc]
      _ = _ := by rw [pow_succ' w (n+1), mul_assoc] <;> rfl
  have hw₀ : w = 0 := by
    apply htUnit.mul_right_cancel
    rw [mul_sub, mul_one, ← hwt, sub_self, zero_mul]
  exact hs (by rw [h, hw₀, zero_pow (by omega : n+2 ≠ 0), zero_mul])

end
end ManuscriptAudit.ReducedFibreRamification

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ReducedFibreRamification.exponent_eq_one
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
