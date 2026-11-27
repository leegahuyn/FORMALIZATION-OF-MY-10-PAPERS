import Lean.Util.CollectAxioms
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Tactic.LinearCombination

/-! The affine Hermitian tangent belongs to the product of the two explicit point ideals. -/

namespace ManuscriptAudit.HermitianTangentIdealMembership

noncomputable section

variable {R : Type*} [CommRing R]

def pointIdeal (U V u v : R) : Ideal R :=
  Ideal.span ({U - u, V - v} : Set R)

def tangent (q : ℕ) (U V u v : R) : R :=
  u ^ q * (U - u) + v ^ q * (V - v)

theorem first_mem (U V u v : R) : U - u ∈ pointIdeal U V u v :=
  Ideal.subset_span (by simp)

theorem second_mem (U V u v : R) : V - v ∈ pointIdeal U V u v :=
  Ideal.subset_span (by simp)

private theorem top_of_unit_mem (I : Ideal R) {x : R} (hx : x ∈ I) (hu : IsUnit x) : I = ⊤ := by
  obtain ⟨u, hu⟩ := hu
  have hm : (u : R) ∈ I := hu.symm ▸ hx
  have hOne : (1 : R) ∈ I := by
    simpa using I.mul_mem_left (↑(u⁻¹) : R) hm
  exact (Ideal.eq_top_iff_one I).mpr hOne

theorem pointIdeal_sup_eq_top (U V u v a b : R)
    (h : IsUnit (u - a) ∨ IsUnit (v - b)) :
    pointIdeal U V u v ⊔ pointIdeal U V a b = ⊤ := by
  let I := pointIdeal U V u v ⊔ pointIdeal U V a b
  rcases h with hu | hv
  · have hm : u - a ∈ I := by
      rw [show u - a = (U - a) - (U - u) by ring]
      exact I.sub_mem ((le_sup_right : pointIdeal U V a b ≤ I) (first_mem U V a b))
        ((le_sup_left : pointIdeal U V u v ≤ I) (first_mem U V u v))
    exact top_of_unit_mem I hm hu
  · have hm : v - b ∈ I := by
      rw [show v - b = (V - b) - (V - v) by ring]
      exact I.sub_mem ((le_sup_right : pointIdeal U V a b ≤ I) (second_mem U V a b))
        ((le_sup_left : pointIdeal U V u v ≤ I) (second_mem U V u v))
    exact top_of_unit_mem I hm hv

variable (E : Type*) [Field E] [Fintype E] [Algebra E R]

local notation "q" => Fintype.card E

theorem frobenius_pairing {u v : R} (h : u ^ (q + 1) + v ^ (q + 1) = 1) :
    u ^ q * u ^ (q * q) + v ^ q * v ^ (q * q) = 1 := by
  let f := FiniteField.frobeniusAlgHom E R
  have hf := congrArg f h
  rw [map_add, map_one] at hf
  change (u ^ (q + 1)) ^ q + (v ^ (q + 1)) ^ q = 1 at hf
  have hp (a : R) : (a ^ (q + 1)) ^ q = a ^ q * a ^ (q * q) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  simpa only [hp] using hf

private theorem tangent_eq_neg_powers {U V u v : R}
    (h : U ^ (q + 1) + V ^ (q + 1) = 1) (hP : u ^ (q + 1) + v ^ (q + 1) = 1) :
    tangent q U V u v = -(U * (U - u) ^ q + V * (V - v) ^ q) := by
  let f := FiniteField.frobeniusAlgHom E R
  have hSub (x y : R) : (x - y) ^ q = x ^ q - y ^ q := map_sub f x y
  rw [tangent, hSub U u, hSub V v]
  rw [pow_succ U q, pow_succ V q] at h
  rw [pow_succ u q, pow_succ v q] at hP
  linear_combination h - hP

theorem tangent_mem_power {U V u v : R}
    (h : U ^ (q + 1) + V ^ (q + 1) = 1) (hP : u ^ (q + 1) + v ^ (q + 1) = 1) :
    tangent q U V u v ∈ pointIdeal U V u v ^ q := by
  let I := pointIdeal U V u v ^ q
  rw [tangent_eq_neg_powers E h hP]
  exact I.neg_mem (I.add_mem
    (I.mul_mem_left U (Ideal.pow_mem_pow (first_mem U V u v) q))
    (I.mul_mem_left V (Ideal.pow_mem_pow (second_mem U V u v) q)))

private theorem tangent_mem_conjugate {U V u v : R} (hP : u ^ (q + 1) + v ^ (q + 1) = 1) :
    tangent q U V u v ∈ pointIdeal U V (u ^ (q * q)) (v ^ (q * q)) := by
  let I := pointIdeal U V (u ^ (q * q)) (v ^ (q * q))
  have hS := frobenius_pairing E hP
  have he : tangent q U V u v =
      u ^ q * (U - u ^ (q * q)) + v ^ q * (V - v ^ (q * q)) := by
    unfold tangent
    rw [pow_succ u q, pow_succ v q] at hP
    linear_combination hS - hP
  rw [he]
  exact I.add_mem (I.mul_mem_left _ (first_mem U V _ _))
    (I.mul_mem_left _ (second_mem U V _ _))

private theorem tangent_mem_next_power_of_fixed {U V u v : R}
    (h : U ^ (q + 1) + V ^ (q + 1) = 1) (hP : u ^ (q + 1) + v ^ (q + 1) = 1)
    (hu : u ^ (q * q) = u) (hv : v ^ (q * q) = v) :
    tangent q U V u v ∈ pointIdeal U V u v ^ (q + 1) := by
  let f := tangent q U V u v
  let I := pointIdeal U V u v
  let F := FiniteField.frobeniusAlgHom E R
  have hPow : f ^ q = u * (U - u) ^ q + v * (V - v) ^ q := by
    change F (u ^ q * (U - u) + v ^ q * (V - v)) = _
    rw [map_add, map_mul, map_mul]
    change (u ^ q) ^ q * (U - u) ^ q + (v ^ q) ^ q * (V - v) ^ q = _
    rw [← pow_mul, ← pow_mul, hu, hv]
  have hSum : f + f ^ q = -((U - u) ^ (q + 1) + (V - v) ^ (q + 1)) := by
    rw [hPow, pow_succ (U - u) q, pow_succ (V - v) q]
    rw [show f = _ from tangent_eq_neg_powers E h hP]
    ring
  have hBig : f ^ q ∈ I ^ (q * q) := by
    rw [pow_mul]
    exact Ideal.pow_mem_pow (tangent_mem_power E h hP) q
  have hq : 1 < q := Fintype.one_lt_card
  have hSmall : q + 1 ≤ q * q := by
    calc
      _ ≤ q + q := Nat.add_le_add_left (Nat.le_of_lt hq) q
      _ = 2 * q := (two_mul q).symm
      _ ≤ _ := Nat.mul_le_mul_right q hq
  have hPmem : f ^ q ∈ I ^ (q + 1) := Ideal.pow_le_pow_right hSmall hBig
  have hSumMem : f + f ^ q ∈ I ^ (q + 1) := by
    rw [hSum]
    exact (I ^ (q + 1)).neg_mem ((I ^ (q + 1)).add_mem
      (Ideal.pow_mem_pow (first_mem U V u v) _) (Ideal.pow_mem_pow (second_mem U V u v) _))
  have hs := (I ^ (q + 1)).sub_mem hSumMem hPmem
  rw [add_sub_cancel_right] at hs
  exact hs

/-- The tangent meets the base point with multiplicity q and its q²-Frobenius conjugate once. -/
theorem tangent_mem_product {U V u v : R}
    (h : U ^ (q + 1) + V ^ (q + 1) = 1) (hP : u ^ (q + 1) + v ^ (q + 1) = 1)
    (hCase : (u ^ (q * q) = u ∧ v ^ (q * q) = v) ∨
      pointIdeal U V u v ⊔ pointIdeal U V (u ^ (q * q)) (v ^ (q * q)) = ⊤) :
    tangent q U V u v ∈ pointIdeal U V u v ^ q * pointIdeal U V (u ^ (q * q)) (v ^ (q * q)) := by
  rcases hCase with ⟨hu, hv⟩ | hCoprime
  · rw [hu, hv, ← pow_succ]
    exact tangent_mem_next_power_of_fixed E h hP hu hv
  · let I := pointIdeal U V u v ^ q
    let J := pointIdeal U V (u ^ (q * q)) (v ^ (q * q))
    have hc : IsCoprime I J := Ideal.isCoprime_iff_sup_eq.mpr (Ideal.pow_sup_eq_top hCoprime)
    change tangent q U V u v ∈ I * J
    rw [← Ideal.inf_eq_mul_of_isCoprime hc]
    exact ⟨tangent_mem_power E h hP, tangent_mem_conjugate E hP⟩

end
end ManuscriptAudit.HermitianTangentIdealMembership

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.HermitianTangentIdealMembership.pointIdeal_sup_eq_top,
      ``ManuscriptAudit.HermitianTangentIdealMembership.frobenius_pairing,
      ``ManuscriptAudit.HermitianTangentIdealMembership.tangent_mem_product] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
