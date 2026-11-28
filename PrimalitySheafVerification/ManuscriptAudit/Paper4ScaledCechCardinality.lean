import Lean.Util.CollectAxioms
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index

/-! For the literal additive inclusions into the lcm residue group,
the printed cardinalities for the two-term complex have the gcd factors reversed. -/

namespace ManuscriptAudit.Paper4ScaledCechCardinality

noncomputable section

private def scaledCast {L : ℕ} (c : ℕ) : ℤ →+ ZMod L where
  toFun x := (c : ZMod L) * (x : ZMod L)
  map_zero' := by simp
  map_add' x y := by simp [mul_add]

private def inclusion {d c L : ℕ} (h : c * d = L) : ZMod d →+ ZMod L :=
  ZMod.lift d ⟨scaledCast c, by
    change (c : ZMod L) * ((d : ℤ) : ZMod L) = 0
    rw [Int.cast_natCast, ← Nat.cast_mul, h, ZMod.natCast_self]⟩

private theorem inclusion_int {d c L : ℕ} (h : c * d = L) (x : ℤ) :
    inclusion h (x : ZMod d) = (c : ZMod L) * (x : ZMod L) :=
  ZMod.lift_coe d _ x

variable (m n : ℕ)

private abbrev g := m.gcd n
private abbrev a := m / g m n
private abbrev b := n / g m n
private abbrev L := m.lcm n

private theorem first_factor : g m n * a m n = m :=
  Nat.mul_div_cancel' (Nat.gcd_dvd_left m n)

private theorem second_factor : g m n * b m n = n :=
  Nat.mul_div_cancel' (Nat.gcd_dvd_right m n)

private theorem cofactors_coprime (hm : m ≠ 0) : (a m n).Coprime (b m n) := by
  have h₀ : 0 < g m n := Nat.gcd_pos_of_pos_left n (Nat.pos_of_ne_zero hm)
  change (a m n).gcd (b m n) = 1
  apply Nat.eq_of_mul_eq_mul_left h₀
  rw [← Nat.gcd_mul_left, first_factor, second_factor, mul_one]

private theorem lcm_factor (hm : m ≠ 0) : L m n = g m n * (a m n * b m n) := by
  calc
    L m n = (g m n * a m n).lcm (g m n * b m n) := by
      rw [first_factor, second_factor]
    _ = g m n * (a m n * b m n) := by
      rw [Nat.lcm_mul_left, (cofactors_coprime m n hm).lcm_eq_mul]

private theorem first_scale (hm : m ≠ 0) : b m n * m = L m n := by
  calc
    b m n * m = b m n * (g m n * a m n) := by rw [first_factor]
    _ = _ := by rw [lcm_factor m n hm]; ac_rfl

private theorem second_scale (hm : m ≠ 0) : a m n * n = L m n := by
  calc
    a m n * n = a m n * (g m n * b m n) := by rw [second_factor]
    _ = _ := by rw [lcm_factor m n hm]; ac_rfl

/-- The additive overlap difference uses the two cyclic inclusions into the
literal lcm residue group, with the same sign as the printed formula. -/
def difference (hm : m ≠ 0) : (ZMod m × ZMod n) →+ ZMod (L m n) :=
  (inclusion (first_scale m n hm)).comp (AddMonoidHom.fst _ _) -
    (inclusion (second_scale m n hm)).comp (AddMonoidHom.snd _ _)

theorem difference_surjective (hm : m ≠ 0) : Function.Surjective (difference m n hm) := by
  intro z
  obtain ⟨x, rfl⟩ := ZMod.intCast_surjective (n := L m n) z
  let u := Nat.gcdA (b m n) (a m n)
  let v := Nat.gcdB (b m n) (a m n)
  have h : (b m n : ℤ) * u + (a m n : ℤ) * v = 1 := by
    have hBezout := Nat.gcd_eq_gcd_ab (b m n) (a m n)
    rw [(cofactors_coprime m n hm).symm.gcd_eq_one, Int.natCast_one] at hBezout
    exact hBezout.symm
  refine ⟨((u * x : ℤ), ((-v) * x : ℤ)), ?_⟩
  change inclusion (first_scale m n hm) ((u * x : ℤ) : ZMod m) -
      inclusion (second_scale m n hm) (((-v) * x : ℤ) : ZMod n) = (x : ZMod (L m n))
  rw [inclusion_int, inclusion_int]
  have hc := congrArg (fun z : ℤ ↦ (z : ZMod (L m n))) h
  push_cast at hc ⊢
  calc
    _ = ((b m n : ZMod (L m n)) * (u : ZMod (L m n)) +
      (a m n : ZMod (L m n)) * (v : ZMod (L m n))) * (x : ZMod (L m n)) := by ring
    _ = _ := by rw [hc, one_mul]

private theorem card_residue (d : ℕ) (hd : d ≠ 0) : Nat.card (ZMod d) = d := by
  letI : NeZero d := ⟨hd⟩
  rw [Nat.card_eq_fintype_card, ZMod.card]

theorem card_range (hm : m ≠ 0) (hn : n ≠ 0) :
    Nat.card (difference m n hm).range = L m n := by
  let e : (difference m n hm).range ≃ ZMod (L m n) :=
    { toFun := Subtype.val
      invFun := fun x ↦ ⟨x, difference_surjective m n hm x⟩
      left_inv := fun _ ↦ Subtype.ext rfl
      right_inv := fun _ ↦ rfl }
  exact (Nat.card_congr e).trans
    (card_residue _ (Nat.lcm_pos (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn)).ne')

theorem card_kernel (hm : m ≠ 0) (hn : n ≠ 0) :
    Nat.card (difference m n hm).ker = g m n := by
  have h := (difference m n hm).ker.card_mul_index
  rw [AddSubgroup.index_ker, card_range m n hm hn, Nat.card_prod,
    card_residue _ hm, card_residue _ hn, ← Nat.gcd_mul_lcm] at h
  exact Nat.eq_of_mul_eq_mul_right
    (Nat.lcm_pos (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn)) h

theorem cokernel_subsingleton (hm : m ≠ 0) :
    Subsingleton (ZMod (L m n) ⧸ (difference m n hm).range) := by
  rw [AddMonoidHom.range_eq_top.mpr (difference_surjective m n hm)]
  exact QuotientAddGroup.subsingleton_quotient_top

end
end ManuscriptAudit.Paper4ScaledCechCardinality

open Lean Elab Command in
run_cmd do
  for name in [``ManuscriptAudit.Paper4ScaledCechCardinality.difference_surjective,
      ``ManuscriptAudit.Paper4ScaledCechCardinality.card_range,
      ``ManuscriptAudit.Paper4ScaledCechCardinality.card_kernel,
      ``ManuscriptAudit.Paper4ScaledCechCardinality.cokernel_subsingleton] do
    let ax ← collectAxioms name
    let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
