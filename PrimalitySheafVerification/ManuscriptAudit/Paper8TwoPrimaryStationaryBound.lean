import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8KloostermanDigitSum
import PrimalitySheafVerification.ManuscriptAudit.Paper8TwoPowerRoots

/-! Bounds for the actual two-primary stationary sums with arbitrary bounded low-digit weights. -/

namespace ManuscriptAudit.Paper8TwoPrimaryStationaryBound

open Finset Paper8KloostermanDigitSum Paper8ProductStationaryPhase Paper8ZModDigitOrthogonality Paper8TwoPowerRoots

noncomputable section

private theorem card_reduceLow_preimage {n d : ℕ} [NeZero n] [NeZero d] (S : Finset (ZMod n)) :
    (Finset.univ.filter (fun z : ZMod (d * n) => (reduceLowDigit z : ZMod n) ∈ S)).card = d * S.card := by
  let e := residueDigitEquiv d n
  have hLow (z : ZMod d × ZMod n) : (reduceLowDigit (e z) : ZMod n) = z.2 := by
    obtain ⟨a, b⟩ := z
    have he : e (a, b) = ((b.val + n * a.val : ℕ) : ZMod (d * n)) := residueDigitEquiv_apply a b
    rw [he, map_natCast, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero,
      ZMod.natCast_zmod_val]
  have hE : Finset.univ.filter (fun z : ZMod (d * n) => (reduceLowDigit z : ZMod n) ∈ S) =
      (Finset.univ.product S).map e.toEmbedding := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · intro hz
      let v := e.symm z
      have he : e v = z := e.apply_symm_apply z
      refine ⟨v, Finset.mem_product.mpr ⟨Finset.mem_univ _, ?_⟩, he⟩
      have h : (reduceLowDigit z : ZMod n) = v.2 := by rw [← he]; exact hLow v
      simpa only [h] using hz
    · rintro ⟨v, hv, rfl⟩
      rw [hLow]
      exact (Finset.mem_product.mp hv).2
  rw [hE, Finset.card_map, Finset.product_eq_sprod, Finset.card_product, Finset.card_univ, ZMod.card]

theorem norm_weighted_kloosterman_two_primary (r : ℕ) {d : ℕ} [NeZero d]
    (w : ZMod (d * (2 * 2 ^ r)) → ℂ) (hw : ∀ z, ‖w z‖ ≤ 1)
    (a b : ZMod ((2 * 2 ^ r) * (d * (2 * 2 ^ r)))) (ha : IsUnit a) (hb : IsUnit b) :
    letI : NeZero (2 * 2 ^ r) := ⟨mul_ne_zero (by decide) (pow_ne_zero _ (by decide))⟩
    ‖weightedKloostermanUnitSum w a b‖ ≤ 4 * (d : ℝ) * ((2 * 2 ^ r : ℕ) : ℝ) := by
  let n := 2 * 2 ^ r
  let m := d * n
  let M := n * m
  letI : NeZero n := ⟨mul_ne_zero (by decide) (pow_ne_zero _ (by decide))⟩
  let μ := @reduceHighDigit n m
  let t := (μ a)⁻¹ * μ b
  let S := Finset.univ.filter (fun x : ZMod n => x ^ 2 = t)
  have hU : IsUnit t := by
    let u := (ha.map μ).unit
    have hU : (u : ZMod n) = μ a := IsUnit.unit_spec _
    unfold t
    rw [← hU, ZMod.inv_coe_unit]
    exact (u⁻¹ : (ZMod n)ˣ).isUnit.mul (hb.map μ)
  have hCount : S.card ≤ 4 := card_two_power_square_unit r t hU
  have hR (z : ZMod m) : μ (z.val : ZMod M) = (reduceLowDigit z : ZMod n) := by
    calc
      _ = (z.val : ZMod n) := map_natCast μ _
      _ = reduceLowDigit ((z.val : ℕ) : ZMod m) := (map_natCast (reduceLowDigit : ZMod m →+* ZMod n) _).symm
      _ = _ := by rw [ZMod.natCast_zmod_val]
  have hP :
      (Finset.univ.filter (fun z : ZMod m => (μ (z.val : ZMod M)) ^ 2 = t)).card = d * S.card := by
    simp_rw [hR]
    change (Finset.univ.filter (fun z : ZMod (d * n) => ((reduceLowDigit z : ZMod n)) ^ 2 = t)).card = _
    have hE : Finset.univ.filter (fun z : ZMod (d * n) => (reduceLowDigit z : ZMod n) ^ 2 = t) =
        Finset.univ.filter (fun z : ZMod (d * n) => (reduceLowDigit z : ZMod n) ∈ S) := by
      ext z
      simp [S]
    rw [hE, card_reduceLow_preimage]
  have hBound := norm_weighted_kloosterman_sum_stationary_count (dvd_mul_left n d) w hw a b ha
  change ‖weightedKloostermanUnitSum w a b‖ ≤ (n : ℝ) *
    ((Finset.univ.filter (fun z : ZMod m => (μ (z.val : ZMod M)) ^ 2 = t)).card : ℝ) at hBound
  rw [hP, Nat.cast_mul] at hBound
  apply hBound.trans
  calc
    _ ≤ (n : ℝ) * ((d : ℝ) * 4) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by exact_mod_cast hCount)
        (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    _ = _ := by change _ = 4 * (d : ℝ) * (n : ℝ); ring

end
end ManuscriptAudit.Paper8TwoPrimaryStationaryBound

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8TwoPrimaryStationaryBound.norm_weighted_kloosterman_two_primary
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
