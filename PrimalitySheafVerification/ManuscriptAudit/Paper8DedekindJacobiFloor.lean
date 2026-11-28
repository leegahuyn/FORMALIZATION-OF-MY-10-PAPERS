import Lean.Util.CollectAxioms
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import PrimalitySheafVerification.ManuscriptAudit.Paper8DedekindFloorReciprocity

/-! Generalized Eisenstein parity for all odd coprime moduli by finite lattice reciprocity. -/

namespace ManuscriptAudit.Paper8DedekindJacobiFloor

open Finset Paper8DedekindFloorParity Paper8DedekindFloorReciprocity

private theorem sign_eq_of_cast_two {a b : ℕ} (h : (a : ZMod 2) = b) :
    (-1 : ℤ) ^ a = (-1 : ℤ) ^ b := by
  have hM := (ZMod.natCast_eq_natCast_iff' a b 2).1 h
  rw [neg_one_pow_eq_pow_mod_two a, neg_one_pow_eq_pow_mod_two b, hM]

private theorem neg_one_pow_square (a : ℕ) : ((-1 : ℤ) ^ a) ^ 2 = 1 := by
  rw [← pow_mul, mul_comm a 2, pow_mul]
  norm_num

private theorem halfFloorWeight_periodic (h k q : ℕ) (hk : 0 < k) :
    (-1 : ℤ) ^ halfFloorWeight (h + 2 * k * q) k =
      (-1 : ℤ) ^ halfFloorWeight h k := by
  apply sign_eq_of_cast_two
  unfold halfFloorWeight
  push_cast
  apply sum_congr rfl
  intro x _
  have hA : (h + 2 * k * q) * (x + 1) = h * (x + 1) + k * (2 * (q * (x + 1))) := by ring
  rw [hA, Nat.add_mul_div_left _ _ hk]
  push_cast
  have hTwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
  simp [hTwo]

private theorem floor_pair {r k x : ℕ} (hk : 0 < k) (hr : r ≤ 2 * k)
    (hC : r.Coprime k) (hx : x < k / 2) :
    r * (x + 1) / k + (2 * k - r) * (x + 1) / k = 2 * x + 1 := by
  let a := r * (x + 1)
  let b := (2 * k - r) * (x + 1)
  have hA : a + b = k * (2 * (x + 1)) := by
    dsimp only [a, b]
    rw [← Nat.add_mul, Nat.add_sub_cancel' hr]
    ring
  have ha0 : a % k ≠ 0 := by
    intro ha
    have hD : k ∣ r * (x + 1) := Nat.dvd_of_mod_eq_zero ha
    have hX := Nat.le_of_dvd (Nat.succ_pos x) (hC.symm.dvd_of_dvd_mul_left hD)
    omega
  let t := a % k + b % k
  have haLt := Nat.mod_lt a hk
  have hbLt := Nat.mod_lt b hk
  have haPos := Nat.pos_of_ne_zero ha0
  have ht0 : 0 < t := by dsimp only [t]; omega
  have ht2 : t < k + k := by dsimp only [t]; omega
  have hT0 : t % k = 0 := by
    dsimp only [t]
    rw [← Nat.add_mod]
    exact Nat.mod_eq_zero_of_dvd ⟨2 * (x + 1), hA⟩
  have hTrep := Nat.mod_add_div t k
  rw [hT0, zero_add] at hTrep
  have hTlt : t / k < 2 := (Nat.div_lt_iff_lt_mul hk).2 (by omega)
  have hTpos : t / k ≠ 0 := by
    intro h
    rw [h, mul_zero] at hTrep
    omega
  have ht : t / k = 1 := by omega
  have hR : a % k + b % k = k := by rw [ht, mul_one] at hTrep; exact hTrep.symm
  have hN : k * (a / k + b / k + 1) = k * (2 * (x + 1)) := by
    calc
      _ = (a % k + k * (a / k)) + (b % k + k * (b / k)) := by
        rw [mul_add, mul_add, mul_one]
        omega
      _ = a + b := by rw [Nat.mod_add_div a k, Nat.mod_add_div b k]
      _ = _ := hA
  have hSum := Nat.eq_of_mul_eq_mul_left hk hN
  change a / k + b / k = _
  omega

private theorem halfFloorWeight_reflect {r k : ℕ} (hk : 0 < k) (hr : r ≤ 2 * k)
    (hC : r.Coprime k) :
    (-1 : ℤ) ^ halfFloorWeight r k =
      (-1 : ℤ) ^ (k / 2) * (-1 : ℤ) ^ halfFloorWeight (2 * k - r) k := by
  have hP : (-1 : ℤ) ^ (halfFloorWeight r k + halfFloorWeight (2 * k - r) k) = (-1 : ℤ) ^ (k / 2) := by
    apply sign_eq_of_cast_two
    unfold halfFloorWeight
    push_cast
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _x ∈ range (k / 2), (1 : ZMod 2) := by
        apply sum_congr rfl
        intro x hx
        rw [← Nat.cast_add, floor_pair hk hr hC (mem_range.mp hx)]
        push_cast
        have hTwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
        simp [hTwo]
      _ = _ := by simp
  calc
    _ = (-1 : ℤ) ^ halfFloorWeight r k * ((-1 : ℤ) ^ halfFloorWeight (2 * k - r) k) ^ 2 := by
      rw [neg_one_pow_square, mul_one]
    _ = _ := by rw [← hP, pow_add]; ring

private theorem jacobi_eq_of_cast {h r k : ℕ} (he : (h : ZMod k) = r) :
    jacobiSym (h : ℤ) k = jacobiSym (r : ℤ) k := by
  apply jacobiSym.mod_left'
  apply (ZMod.intCast_eq_intCast_iff' _ _ k).1
  simpa only [Int.cast_natCast] using he

private theorem half_floor_sign_reciprocity {h k : ℕ} (hh : h % 2 = 1) (hk : k % 2 = 1)
    (hC : h.Coprime k) :
    (-1 : ℤ) ^ halfFloorWeight h k =
      (-1 : ℤ) ^ (h / 2 * (k / 2)) * (-1 : ℤ) ^ halfFloorWeight k h := by
  rw [mul_comm (h / 2) (k / 2), ← halfFloorWeight_reciprocity hh hk hC, pow_add]
  calc
    _ = (-1 : ℤ) ^ halfFloorWeight h k * ((-1 : ℤ) ^ halfFloorWeight k h) ^ 2 := by
      rw [neg_one_pow_square, mul_one]
    _ = _ := by ring

theorem jacobiSym_eq_half_floor (h k : ℕ) (hh : h % 2 = 1) (hk : k % 2 = 1)
    (hC : h.Coprime k) : jacobiSym (h : ℤ) k = (-1 : ℤ) ^ halfFloorWeight h k := by
  induction k using Nat.strong_induction_on generalizing h with
  | h k ih =>
    have hk0 : 0 < k := by omega
    by_cases hk1 : k = 1
    · subst k
      simp [halfFloorWeight, jacobiSym.one_right]
    let r := h % (2 * k)
    let q := h / (2 * k)
    have hR : r + 2 * k * q = h := Nat.mod_add_div h (2 * k)
    have hRlt : r < 2 * k := Nat.mod_lt h (by omega)
    have hRodd : r % 2 = 1 := by
      have h := congrArg (fun a : ℕ => a % 2) hR
      change (r + 2 * k * q) % 2 = h % 2 at h
      have hz : (2 * k * q) % 2 = 0 := by rw [Nat.mul_assoc, Nat.mul_mod_right]
      rw [Nat.add_mod, hz, Nat.add_zero, Nat.mod_mod, hh] at h
      exact h
    have hRcast : (r : ZMod k) = h := by
      have hf := congrArg (fun a : ℕ => (a : ZMod k)) hR
      push_cast at hf
      simpa only [ZMod.natCast_self, mul_zero, zero_mul, add_zero] using hf
    have hRC : r.Coprime k := (ZMod.isUnit_iff_coprime r k).1 <| by
      rw [hRcast]
      exact (ZMod.unitOfCoprime h hC).isUnit
    have hRne : r ≠ k := by
      intro he
      rw [he, Nat.coprime_iff_gcd_eq_one, Nat.gcd_self] at hRC
      exact hk1 hRC
    have hSmall (u : ℕ) (hu : u < k) (huo : u % 2 = 1) (huC : u.Coprime k) :
        jacobiSym (u : ℤ) k = (-1 : ℤ) ^ halfFloorWeight u k := by
      rw [jacobiSym.quadratic_reciprocity (odd_iff.mpr huo) (odd_iff.mpr hk),
        ih u hu k hk huo huC.symm, ← half_floor_sign_reciprocity huo hk huC]
    rw [← jacobi_eq_of_cast hRcast, ← hR, halfFloorWeight_periodic r k q hk0]
    by_cases hlt : r < k
    · exact hSmall r hlt hRodd hRC
    let u := 2 * k - r
    have hU : u + r = 2 * k := Nat.sub_add_cancel hRlt.le
    have hu : u < k := by omega
    have huo : u % 2 = 1 := by
      have h := congrArg (fun a : ℕ => a % 2) hU
      rw [Nat.add_mod, hRodd, Nat.mul_mod_right] at h
      omega
    have hUCst : (u : ZMod k) = -(r : ZMod k) := by
      apply eq_neg_of_add_eq_zero_left
      have h := congrArg (fun a : ℕ => (a : ZMod k)) hU
      push_cast at h
      simpa only [ZMod.natCast_self, mul_zero] using h
    have huC : u.Coprime k := (ZMod.isUnit_iff_coprime u k).1 <| by
      rw [hUCst]
      exact (ZMod.unitOfCoprime r hRC).isUnit.neg
    have hJ : jacobiSym (r : ℤ) k = jacobiSym (-(u : ℤ)) k := by
      apply jacobiSym.mod_left'
      apply (ZMod.intCast_eq_intCast_iff' _ _ k).1
      push_cast
      rw [hUCst, neg_neg]
    rw [hJ, jacobiSym.neg _ (odd_iff.mpr hk), χ₄_eq_neg_one_pow hk, hSmall u hu huo huC]
    exact (halfFloorWeight_reflect hk0 hRlt.le hRC).symm

theorem jacobiSym_eq_weighted_floor (h k : ℕ) (hh : h % 2 = 1) (hk : k % 2 = 1)
    (hC : h.Coprime k) : jacobiSym (h : ℤ) k = (-1 : ℤ) ^ dedekindFloorWeight h k := by
  rw [jacobiSym_eq_half_floor h k hh hk hC]
  apply sign_eq_of_cast_two
  exact (ZMod.natCast_eq_natCast_iff' _ _ 2).2 (dedekindFloorWeight_parity hh hk hC).symm

end ManuscriptAudit.Paper8DedekindJacobiFloor

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8DedekindJacobiFloor.jacobiSym_eq_half_floor,
      ``ManuscriptAudit.Paper8DedekindJacobiFloor.jacobiSym_eq_weighted_floor] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
