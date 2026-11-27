import Lean.Util.CollectAxioms
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! Finite-field inputs to the centered Hermitian covering argument. -/

namespace ManuscriptAudit.CubicHermitianFiniteInputs

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

/-- Over an algebraically closed field, each order prime to the characteristic has a primitive root. -/
theorem exists_primitive_root [IsAlgClosed K] (m : ℕ) [NeZero m] (hm : (m : K) ≠ 0) :
    ∃ z : K, IsPrimitiveRoot z m := by
  classical
  let f : K[X] := X ^ m - C 1
  have hsep : f.Separable := separable_X_pow_sub_C 1 hm one_ne_zero
  have hRoots : f.roots.card = m := by
    rw [← (IsAlgClosed.splits f).natDegree_eq_card_roots]
    exact natDegree_X_pow_sub_C
  apply card_rootsOfUnity_eq_iff_exists_isPrimitiveRoot.mp
  calc
    _ = Nat.card {x // x ∈ nthRoots m (1 : K)} :=
      Nat.card_congr (rootsOfUnityEquivNthRoots K m)
    _ = (nthRoots m (1 : K)).toFinset.card :=
      Nat.subtype_card _ (fun _ => Multiset.mem_toFinset)
    _ = m := by
      change f.roots.toFinset.card = m
      rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep), hRoots]

variable (E : Type*) [Field E] [Fintype E]
variable (K : Type*) [Field K] [Algebra E K]

local notation "q" => Fintype.card E

theorem cast_divisor_add_one_ne_zero {m : ℕ} (hm : m ∣ q + 1) : (m : K) ≠ 0 := by
  obtain ⟨k, hk⟩ := hm
  have hq : (q : K) = 0 := by
    rw [← map_natCast (algebraMap E K), FiniteField.cast_card_eq_zero E, map_zero]
  have hone : ((q + 1 : ℕ) : K) = 1 := by rw [Nat.cast_add, hq, Nat.cast_one, zero_add]
  intro h
  rw [hk, Nat.cast_mul, h, zero_mul] at hone
  exact zero_ne_one hone

/-- Roots of a scalar equation of degree dividing q+1 are fixed by the q²-power map. -/
theorem root_frobenius_sq_fixed {m : ℕ} (hm : m ∣ q + 1) {a : E} (ha : a ≠ 0) {x : K}
    (hx : x ^ m = algebraMap E K a) : x ^ (q * q) = x := by
  obtain ⟨k, hk⟩ := hm
  have hq : 1 ≤ q := Fintype.card_pos
  have hExp : q * q = (q + 1) * (q - 1) + 1 := by
    have hAdd : (q + 1) * (q - 1) + (q + 1) = (q + 1) * q := calc
      _ = (q + 1) * ((q - 1) + 1) := by rw [mul_add, mul_one]
      _ = _ := by rw [Nat.sub_add_cancel hq]
    have hMul : (q + 1) * q = q * q + q := by rw [add_mul, one_mul]
    have h := hAdd.trans hMul
    omega
  have hPow : x ^ (q + 1) = algebraMap E K (a ^ k) := by
    rw [hk, pow_mul, hx, map_pow]
  rw [hExp, pow_succ, pow_mul, hPow, ← map_pow,
    FiniteField.pow_card_sub_one_eq_one _ (pow_ne_zero k ha), map_one, one_mul]

/-- Cubing is onto when q is congruent to two modulo three. -/
theorem exists_cube_base (hq : q % 3 = 2) (a : E) : ∃ b : E, b ^ 3 = a := by
  let d := (2 * q - 1) / 3
  have hd : d * 3 = (q - 1) * 2 + 1 := by dsimp only [d]; omega
  refine ⟨a ^ d, ?_⟩
  rw [← pow_mul, hd, pow_succ, pow_mul]
  by_cases ha : a = 0
  · rw [ha, mul_zero]
  · rw [FiniteField.pow_card_sub_one_eq_one a ha, one_pow, one_mul]

theorem normalized_endpoint_scales [IsAlgClosed K] {A : E} (hA : A ≠ 0)
    (hq3 : q % 3 = 2) (hq2 : q % 2 = 1) :
    ∃ α β : K, α ^ 3 = -(algebraMap E K A) ∧ β ^ 2 = algebraMap E K A ∧
      α ^ (q * q) = α ∧ β ^ (q * q) = β := by
  obtain ⟨a, ha⟩ := exists_cube_base E hq3 (-A)
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap E K A) zero_lt_two
  refine ⟨algebraMap E K a, b, ?_, hb, ?_, ?_⟩
  · rw [← map_pow, ha, map_neg]
  · rw [← map_pow, pow_mul, FiniteField.pow_card, FiniteField.pow_card]
  · exact root_frobenius_sq_fixed E K (by omega : 2 ∣ q + 1) hA hb

end
end ManuscriptAudit.CubicHermitianFiniteInputs

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicHermitianFiniteInputs.exists_primitive_root,
      ``ManuscriptAudit.CubicHermitianFiniteInputs.cast_divisor_add_one_ne_zero,
      ``ManuscriptAudit.CubicHermitianFiniteInputs.root_frobenius_sq_fixed,
      ``ManuscriptAudit.CubicHermitianFiniteInputs.exists_cube_base,
      ``ManuscriptAudit.CubicHermitianFiniteInputs.normalized_endpoint_scales] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
