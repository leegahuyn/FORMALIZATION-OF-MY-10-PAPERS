import Lean.Util.CollectAxioms
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic.Ring

/-! Cube roots of unity determine the sign of Frobenius on a square root of minus three. -/

namespace ManuscriptAudit.CubicThreeFrobeniusSigns

noncomputable section

variable {K : Type*} [Field K]

def signed (s : Bool) (x : K) : K := if s then x else -x

def signScalar (s : Bool) : ZMod 3 := if s then 1 else -1

theorem signed_mul (s t : Bool) (x y : K) :
    signed s x * signed t y = signed (s == t) (x * y) := by
  cases s <;> cases t <;> simp [signed]

theorem signed_div (s : Bool) (x y : K) :
    signed s x / y = signed s (x / y) := by
  cases s <;> simp [signed]

theorem signScalar_mul (s t : Bool) :
    signScalar s * signScalar t = signScalar (s == t) := by
  cases s <;> cases t <;> decide

theorem signScalar_add_of_ne {s t : Bool} (h : s ≠ t) :
    signScalar s + signScalar t = 0 := by
  cases s <;> cases t <;> (first | contradiction | decide)

theorem signScalar_add_self (s : Bool) : signScalar s + signScalar s = -signScalar s := by
  cases s <;> decide

private def cubeRoot (s : K) : K := (s - 1) / 2

private theorem cubeRoot_spec (h₂ : (2 : K) ≠ 0) {s : K} (hs : s ^ 2 = -(3 : K)) :
    2 * cubeRoot s + 1 = s ∧ cubeRoot s ^ 2 + cubeRoot s + 1 = 0 ∧ cubeRoot s ^ 3 = 1 := by
  let z := cubeRoot s
  have hz : (2 : K) * z = s - 1 := by
    change 2 * ((s - 1) / 2) = _
    rw [mul_comm, div_mul_cancel₀ _ h₂]
  have hsum : (2 : K) * z + 1 = s := by rw [hz, sub_add_cancel]
  have hcycl : z ^ 2 + z + 1 = 0 := by
    have h : (2 : K) ^ 2 * (z ^ 2 + z + 1) = s ^ 2 + 3 := by
      calc
        _ = ((2 : K) * z) ^ 2 + 2 * (2 * z) + 4 := by ring
        _ = _ := by rw [hz]; ring
    rw [hs, neg_add_cancel] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ h₂)
  refine ⟨hsum, hcycl, sub_eq_zero.mp ?_⟩
  calc
    z ^ 3 - 1 = (z - 1) * (z ^ 2 + z + 1) := by ring
    _ = 0 := by rw [hcycl, mul_zero]

theorem pow_cube_reduce (x : K) (q : ℕ) (hx : x ^ 3 = 1) :
    x ^ q = x ^ (q % 3) := by
  calc
    _ = x ^ (q % 3 + 3 * (q / 3)) := congrArg (fun n : ℕ => x ^ n) (Nat.mod_add_div q 3).symm
    _ = _ := by rw [pow_add, pow_mul, hx, one_pow, mul_one]

/-- An actual q-power field map acts on a square root of minus three by the q residue sign. -/
theorem map_sqrt_neg_three (q : ℕ) (σ : K →+* K) (hσ : ∀ x : K, σ x = x ^ q)
    (hq : q % 3 ≠ 0) (h₂ : (2 : K) ≠ 0) {s : K} (hs : s ^ 2 = -(3 : K)) :
    σ s = signed (decide (q % 3 = 1)) s := by
  let z := cubeRoot s
  obtain ⟨hsum, hcycl, hcube⟩ := cubeRoot_spec h₂ hs
  change 2 * z + 1 = s at hsum
  change z ^ 2 + z + 1 = 0 at hcycl
  change z ^ 3 = 1 at hcube
  have hm : σ s = 2 * z ^ (q % 3) + 1 := by
    calc
      _ = σ (2 * z + 1) := congrArg σ hsum.symm
      _ = 2 * σ z + 1 := by simp
      _ = _ := by rw [hσ z, pow_cube_reduce z q hcube]
  by_cases hr : q % 3 = 1
  · have hpos : σ s = s := hm.trans (by simpa [hr] using hsum)
    simpa [signed, hr] using hpos
  · have hr' : q % 3 = 2 := by omega
    have hneg : σ s = -s := by
      calc
        σ s = 2 * z ^ 2 + 1 := by simpa only [hr'] using hm
        _ = 2 * (z ^ 2 + z + 1) - (2 * z + 1) := by ring
        _ = -s := by rw [hcycl, mul_zero, zero_sub, hsum]
    simpa [signed, hr] using hneg

/-- In the cardinality-one residue class the finite field contains a primitive cube root. -/
theorem finite_exists_primitive_cube_root [Fintype K] (hq : Fintype.card K % 3 = 1) :
    ∃ z : K, IsPrimitiveRoot z 3 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hpr : IsPrimitiveRoot g (Nat.card Kˣ) := IsPrimitiveRoot.iff_orderOf.mpr hg
  have hc : Nat.card Kˣ = Fintype.card K - 1 := by rw [Nat.card_eq_fintype_card, Fintype.card_units]
  have hp : 0 < Nat.card Kˣ := Nat.card_pos
  have he : Nat.card Kˣ = ((Fintype.card K - 1) / 3) * 3 := by rw [hc]; omega
  exact ⟨_, IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.pow hp hpr he)⟩

end
end ManuscriptAudit.CubicThreeFrobeniusSigns

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicThreeFrobeniusSigns.signed_mul,
      ``ManuscriptAudit.CubicThreeFrobeniusSigns.signScalar_mul,
      ``ManuscriptAudit.CubicThreeFrobeniusSigns.map_sqrt_neg_three,
      ``ManuscriptAudit.CubicThreeFrobeniusSigns.finite_exists_primitive_cube_root] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
