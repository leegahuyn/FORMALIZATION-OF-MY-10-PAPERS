import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8ProductStationaryPhase

/-! The exact four-branch upper bound for square roots of unity at powers of two. -/

namespace ManuscriptAudit.Paper8TwoPowerRoots

open Finset Paper8ProductStationaryPhase Paper8ZModDigitOrthogonality

noncomputable section

private theorem pow_two_dvd_sub_or_add {r x : ℕ} (hx : 0 < x)
    (hDiv : 2 * 2 ^ r ∣ (x - 1) * (x + 1)) :
    2 ^ r ∣ x - 1 ∨ 2 ^ r ∣ x + 1 := by
  let k := 2 ^ r
  have hMod : ((x - 1) * (x + 1)) % 2 = 0 :=
    Nat.mod_eq_zero_of_dvd ((dvd_mul_right 2 k).trans hDiv)
  have hxOdd : x % 2 = 1 := by
    by_contra h
    have hL : (x - 1) % 2 = 1 := by omega
    have hR : (x + 1) % 2 = 1 := by omega
    rw [Nat.mul_mod, hL, hR] at hMod
    norm_num at hMod
  let L := (x - 1) / 2
  let R := (x + 1) / 2
  have hL : x - 1 = 2 * L := by unfold L; omega
  have hR : x + 1 = 2 * R := by unfold R; omega
  have hNext : R = L + 1 := by omega
  obtain ⟨q, hq⟩ := hDiv
  have hDivR : k ∣ (x - 1) * R := by
    refine ⟨q, Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) ?_⟩
    calc
      _ = (x - 1) * (x + 1) := by rw [hR]; ring
      _ = _ := by rw [hq]; unfold k; ring
  have hDivL : k ∣ L * (x + 1) := by
    refine ⟨q, Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) ?_⟩
    calc
      _ = (x - 1) * (x + 1) := by rw [hL] <;> ring
      _ = _ := by rw [hq]; unfold k; ring
  by_cases hOdd : R % 2 = 1
  · have hCop : k.Coprime R := (Nat.prime_two.coprime_iff_not_dvd.2 (fun h => by
      have hZ := Nat.mod_eq_zero_of_dvd h
      omega)).pow_left r
    exact Or.inl (hCop.dvd_of_dvd_mul_right hDivR)
  · have hOther : L % 2 = 1 := by omega
    have hCop : k.Coprime L := (Nat.prime_two.coprime_iff_not_dvd.2 (fun h => by
      have hZ := Nat.mod_eq_zero_of_dvd h
      omega)).pow_left r
    exact Or.inr (hCop.dvd_of_dvd_mul_left hDivL)

theorem two_power_square_one_reduce (r : ℕ) (u : ZMod (2 * 2 ^ r)) (hu : u ^ 2 = 1) :
    (reduceLowDigit u : ZMod (2 ^ r)) = 1 ∨ (reduceLowDigit u : ZMod (2 ^ r)) = -1 := by
  let k := 2 ^ r
  let M := 2 * k
  have hk : 0 < k := pow_pos (by decide) _
  letI : NeZero k := ⟨hk.ne'⟩
  let x := u.val + M
  have hx : 0 < x := by unfold x M; omega
  have hX : (x : ZMod M) = u := by
    unfold x
    rw [Nat.cast_add, ZMod.natCast_self, add_zero, ZMod.natCast_zmod_val]
  have hm : ((x - 1 : ℕ) : ZMod M) = u - 1 := by
    rw [Nat.cast_sub (show 1 ≤ x from hx), Nat.cast_one, hX]
  have hp : ((x + 1 : ℕ) : ZMod M) = u + 1 := by
    rw [Nat.cast_add x 1, Nat.cast_one, hX]
  have hd : M ∣ (x - 1) * (x + 1) := by
    apply (ZMod.natCast_eq_zero_iff _ M).1
    rw [Nat.cast_mul, hm, hp, show (u - 1) * (u + 1) = u ^ 2 - 1 by ring, hu, sub_self]
  have hfx : (x : ZMod k) = reduceLowDigit u := by
    have h := congrArg (@reduceLowDigit 2 k) hX
    rw [map_natCast] at h
    exact h
  rcases pow_two_dvd_sub_or_add hx hd with h | h
  · left
    have h0 := (ZMod.natCast_eq_zero_iff (x - 1) k).2 h
    rw [Nat.cast_sub (show 1 ≤ x from hx), Nat.cast_one, hfx] at h0
    exact sub_eq_zero.mp h0
  · right
    have h0 := (ZMod.natCast_eq_zero_iff (x + 1) k).2 h
    rw [Nat.cast_add x 1, Nat.cast_one, hfx] at h0
    exact eq_neg_of_add_eq_zero_left h0

theorem card_two_power_square_one (r : ℕ) :
    (Finset.univ.filter (fun u : ZMod (2 * 2 ^ r) => u ^ 2 = 1)).card ≤ 4 := by
  let k := 2 ^ r
  letI : NeZero k := ⟨pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0)⟩
  let e := residueDigitEquiv 2 k
  let S := Finset.univ.filter (fun u : ZMod (2 * k) => u ^ 2 = 1)
  let C : Finset (ZMod k) := {1, -1}
  have hLow (z : ZMod 2 × ZMod k) : (reduceLowDigit (e z) : ZMod k) = z.2 := by
    obtain ⟨a, b⟩ := z
    have he : e (a, b) = ((b.val + k * a.val : ℕ) : ZMod (2 * k)) := residueDigitEquiv_apply a b
    rw [he, map_natCast, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero,
      ZMod.natCast_zmod_val]
  have hS : S ⊆ (Finset.univ.product C).map e.toEmbedding := by
    intro u hu
    have hu' : u ^ 2 = 1 := (Finset.mem_filter.mp hu).2
    have hR := two_power_square_one_reduce r u hu'
    let z := e.symm u
    have he : e z = u := e.apply_symm_apply u
    have hl : (reduceLowDigit u : ZMod k) = z.2 := by
      rw [← he]
      exact hLow z
    apply Finset.mem_map.mpr
    refine ⟨z, Finset.mem_product.mpr ⟨Finset.mem_univ _, ?_⟩, he⟩
    rw [hl] at hR
    simpa only [C, Finset.mem_insert, Finset.mem_singleton] using hR
  have hCard : C.card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
  change S.card ≤ 4
  apply (Finset.card_le_card hS).trans
  rw [Finset.card_map, Finset.card_product, Finset.card_univ, ZMod.card]
  omega

theorem card_two_power_square_unit (r : ℕ) (a : ZMod (2 * 2 ^ r)) (ha : IsUnit a) :
    (Finset.univ.filter (fun u : ZMod (2 * 2 ^ r) => u ^ 2 = a)).card ≤ 4 := by
  let M := 2 * 2 ^ r
  let S := Finset.univ.filter (fun u : ZMod M => u ^ 2 = a)
  let T := Finset.univ.filter (fun u : ZMod M => u ^ 2 = 1)
  by_cases hS : ∃ x : ZMod M, x ^ 2 = a
  · obtain ⟨x, hx⟩ := hS
    have hV : x * (x * a⁻¹) = 1 := by
      rw [← mul_assoc, ← pow_two, hx, ZMod.mul_inv_of_unit a ha]
    have hU : IsUnit x := ⟨⟨x, x * a⁻¹, hV, by simpa only [mul_comm] using hV⟩, rfl⟩
    let e : Equiv.Perm (ZMod M) :=
      { toFun := fun z => z * x⁻¹
        invFun := fun z => z * x
        left_inv := fun z => by rw [mul_assoc, ZMod.inv_mul_of_unit x hU, mul_one]
        right_inv := fun z => by rw [mul_assoc, ZMod.mul_inv_of_unit x hU, mul_one] }
    have hMap : S.map e.toEmbedding ⊆ T := by
      intro z hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hz
      have hY := (Finset.mem_filter.mp hy).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      change (y * x⁻¹) ^ 2 = 1
      rw [mul_pow, hY, ← hx, ← mul_pow, ZMod.mul_inv_of_unit x hU, one_pow]
    calc
      _ = (S.map e.toEmbedding).card := by rw [Finset.card_map]
      _ ≤ T.card := Finset.card_le_card hMap
      _ ≤ _ := card_two_power_square_one r
  · have hEmpty : S = ∅ := by
      ext x
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      exact fun h => hS ⟨x, h⟩
    change S.card ≤ _
    rw [hEmpty, Finset.card_empty]
    omega

end
end ManuscriptAudit.Paper8TwoPowerRoots

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8TwoPowerRoots.card_two_power_square_unit
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
