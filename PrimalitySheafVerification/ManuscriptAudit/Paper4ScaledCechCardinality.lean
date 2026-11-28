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

/-- On integer representatives the scale factors are the two literal lcm quotients. -/
theorem difference_int (hm : m ≠ 0) (hn : n ≠ 0) (x y : ℤ) :
    difference m n hm ((x : ZMod m), (y : ZMod n)) =
      ((L m n / m : ℕ) : ZMod (L m n)) * (x : ZMod (L m n)) -
        ((L m n / n : ℕ) : ZMod (L m n)) * (y : ZMod (L m n)) := by
  have h₁ : L m n / m = b m n := by
    rw [← first_scale m n hm, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm)]
  have h₂ : L m n / n = a m n := by
    rw [← second_scale m n hm, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hn)]
  change inclusion (first_scale m n hm) (x : ZMod m) -
    inclusion (second_scale m n hm) (y : ZMod n) = _
  rw [inclusion_int, inclusion_int, h₁, h₂]

theorem difference_surjective (hm : m ≠ 0) : Function.Surjective (difference m n hm) := by
  intro z
  obtain ⟨x, rfl⟩ := ZMod.intCast_surjective (n := L m n) z
  let u := Nat.gcdA (b m n) (a m n)
  let v := Nat.gcdB (b m n) (a m n)
  have h : (b m n : ℤ) * u + (a m n : ℤ) * v = 1 := by
    have hBezout := Nat.gcd_eq_gcd_ab (b m n) (a m n)
    rw [(cofactors_coprime m n hm).symm.gcd_eq_one, Int.natCast_one] at hBezout
    exact hBezout.symm
  refine ⟨(((u * x : ℤ) : ZMod m), (((-v) * x : ℤ) : ZMod n)), ?_⟩
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
    card_residue _ hm, card_residue _ hn, ← Nat.gcd_mul_lcm m n] at h
  exact Nat.eq_of_mul_eq_mul_right
    (Nat.lcm_pos (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn)) h

theorem cokernel_subsingleton (hm : m ≠ 0) :
    Subsingleton (ZMod (L m n) ⧸ (difference m n hm).range) := by
  rw [AddMonoidHom.range_eq_top.mpr (difference_surjective m n hm)]
  exact QuotientAddGroup.subsingleton_quotient_top

private theorem inclusion_injective {d c L : ℕ} (h : c * d = L) (hc : 0 < c) :
    Function.Injective (inclusion h) := by
  intro x y hxy
  apply sub_eq_zero.mp
  have hZero : inclusion h (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  obtain ⟨r, hr⟩ := ZMod.intCast_surjective (n := d) (x - y)
  rw [← hr, inclusion_int] at hZero
  have hCast : (((c : ℤ) * r : ℤ) : ZMod L) = 0 := by
    rw [Int.cast_mul, Int.cast_natCast]
    exact hZero
  have hDiv := (ZMod.intCast_zmod_eq_zero_iff_dvd ((c : ℤ) * r) L).mp hCast
  have hL : (L : ℤ) = (c : ℤ) * (d : ℤ) := by exact_mod_cast h.symm
  rw [hL] at hDiv
  have hd : (d : ℤ) ∣ r := (Int.mul_dvd_mul_iff_left (Int.ofNat_ne_zero.mpr hc.ne')).mp hDiv
  rw [← hr]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd r d).mpr hd

/-- The actual kernel is the cyclic gcd group, embedded by the two cofactor scalings. -/
def kernelEquiv (hm : m ≠ 0) (hn : n ≠ 0) :
    ZMod (g m n) ≃+ (difference m n hm).ker := by
  letI : NeZero m := ⟨hm⟩
  letI : NeZero n := ⟨hn⟩
  have hg : 0 < g m n := Nat.gcd_pos_of_pos_left n (Nat.pos_of_ne_zero hm)
  have ha : a m n * g m n = m := (Nat.mul_comm _ _).trans (first_factor m n)
  have hb : b m n * g m n = n := (Nat.mul_comm _ _).trans (second_factor m n)
  let P := (inclusion ha).prod (inclusion hb)
  let j : ZMod (g m n) →+ (difference m n hm).ker :=
    P.codRestrict _ (by
      intro z
      obtain ⟨r, rfl⟩ := ZMod.intCast_surjective (n := g m n) z
      change inclusion (first_scale m n hm) (inclusion ha (r : ZMod (g m n))) -
        inclusion (second_scale m n hm) (inclusion hb (r : ZMod (g m n))) = 0
      have hA : inclusion ha (r : ZMod (g m n)) = (((a m n : ℤ) * r : ℤ) : ZMod m) := by
        rw [inclusion_int, Int.cast_mul, Int.cast_natCast]
      have hB : inclusion hb (r : ZMod (g m n)) = (((b m n : ℤ) * r : ℤ) : ZMod n) := by
        rw [inclusion_int, Int.cast_mul, Int.cast_natCast]
      rw [hA, hB, inclusion_int, inclusion_int]
      push_cast
      ring)
  refine AddEquiv.ofBijective j ((Nat.bijective_iff_injective_and_card j).mpr ⟨?_, ?_⟩)
  · intro x y hxy
    exact (inclusion_injective ha (Nat.div_gcd_pos_of_pos_left n (Nat.pos_of_ne_zero hm)))
      (congrArg (fun z : (difference m n hm).ker ↦ z.val.1) hxy)
  · rw [card_residue _ hg.ne', card_kernel m n hm hn]

theorem card_cokernel (hm : m ≠ 0) :
    Nat.card (ZMod (L m n) ⧸ (difference m n hm).range) = 1 := by
  letI := cokernel_subsingleton m n hm
  let e : (ZMod (L m n) ⧸ (difference m n hm).range) ≃ PUnit :=
    { toFun := fun _ ↦ PUnit.unit
      invFun := fun _ ↦ 0
      left_inv := fun _ ↦ Subsingleton.elim _ _
      right_inv := fun _ ↦ Subsingleton.elim _ _ }
  simpa using Nat.card_congr e

/-- Each printed cardinality fails for nontrivial gcd in this overlap model. -/
theorem printed_cardinalities_fail (hm : m ≠ 0) (hn : n ≠ 0) (hg : 1 < g m n) :
    Nat.card (difference m n hm).range ≠ L m n / g m n ∧
      Nat.card (difference m n hm).ker ≠ (g m n)^2 ∧
      Nat.card (ZMod (L m n) ⧸ (difference m n hm).range) ≠ g m n := by
  rw [card_range m n hm hn, card_kernel m n hm hn, card_cokernel m n hm]
  have hL : 0 < L m n := Nat.lcm_pos (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn)
  have hg' : 0 < g m n := Nat.zero_lt_of_lt hg
  have hSquare : g m n < (g m n)^2 := by
    simpa only [pow_two, Nat.mul_one] using Nat.mul_lt_mul_of_pos_left hg hg'
  exact ⟨(Nat.div_lt_self hL hg).ne', hSquare.ne, hg.ne⟩

end
end ManuscriptAudit.Paper4ScaledCechCardinality

open Lean Elab Command in
run_cmd do
  for name in [``ManuscriptAudit.Paper4ScaledCechCardinality.difference_int,
      ``ManuscriptAudit.Paper4ScaledCechCardinality.difference_surjective,
      ``ManuscriptAudit.Paper4ScaledCechCardinality.card_range,
      ``ManuscriptAudit.Paper4ScaledCechCardinality.card_kernel,
      ``ManuscriptAudit.Paper4ScaledCechCardinality.cokernel_subsingleton,
      ``ManuscriptAudit.Paper4ScaledCechCardinality.kernelEquiv,
      ``ManuscriptAudit.Paper4ScaledCechCardinality.card_cokernel,
      ``ManuscriptAudit.Paper4ScaledCechCardinality.printed_cardinalities_fail] do
    let ax ← collectAxioms name
    let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
