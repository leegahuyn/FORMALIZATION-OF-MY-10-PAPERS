import Lean.Util.CollectAxioms
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.Ring

/-!
Paper 4, physical p. 116, Theorem 3.23 uses the additive inclusions of
the residue groups of orders M and N into order L = lcm(M,N). Their
difference is always surjective for positive M and N.
-/

namespace ManuscriptAudit.CyclicInclusionCokernel

private theorem gcd_lcm_quotients (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    Nat.gcd (m.lcm n / m) (m.lcm n / n) = 1 := by
  let L := m.lcm n
  let d := Nat.gcd (L / m) (L / n)
  change d = 1
  have hL : 0 < L := Nat.lcm_pos hm hn
  have hmL : m ∣ L := Nat.dvd_lcm_left m n
  have hnL : n ∣ L := Nat.dvd_lcm_right m n
  have hd : 0 < d :=
    Nat.gcd_pos_of_pos_left _ (Nat.div_pos (Nat.le_of_dvd hL hmL) hm)
  obtain ⟨a, ha⟩ := Nat.gcd_dvd_left (L / m) (L / n)
  obtain ⟨b, hb⟩ := Nat.gcd_dvd_right (L / m) (L / n)
  change L / m = d * a at ha
  change L / n = d * b at hb
  have hma : L = d * (a * m) := calc
    L = (L / m) * m := (Nat.div_mul_cancel hmL).symm
    _ = d * (a * m) := by rw [ha, Nat.mul_assoc]
  have hnb : L = d * (b * n) := calc
    L = (L / n) * n := (Nat.div_mul_cancel hnL).symm
    _ = d * (b * n) := by rw [hb, Nat.mul_assoc]
  have h1 : m ∣ L / d := ⟨a, by
    calc
      L / d = d * (a * m) / d := congrArg (fun t : ℕ => t / d) hma
      _ = a * m := Nat.mul_div_cancel_left _ hd
      _ = m * a := Nat.mul_comm _ _⟩
  have h2 : n ∣ L / d := ⟨b, by
    calc
      L / d = d * (b * n) / d := congrArg (fun t : ℕ => t / d) hnb
      _ = b * n := Nat.mul_div_cancel_left _ hd
      _ = n * b := Nat.mul_comm _ _⟩
  have hdL : d ∣ L := ⟨a * m, hma⟩
  have hEq : L / d = L :=
    Nat.dvd_antisymm ⟨d, (Nat.div_mul_cancel hdL).symm⟩ (Nat.lcm_dvd h1 h2)
  apply Nat.eq_of_mul_eq_mul_left hL
  calc
    L * d = (L / d) * d := congrArg (fun t : ℕ => t * d) hEq.symm
    _ = L * 1 := by rw [Nat.div_mul_cancel hdL, Nat.mul_one]

private def scaledIntCast {L : ℕ} (c : ZMod L) : ℤ →+ ZMod L where
  toFun x := c * (x : ZMod L)
  map_zero' := by simp
  map_add' x y := by simp [mul_add]

/-- Additive map induced by multiplication by L/d on integer representatives. -/
def cyclicInclusion {L d : ℕ} (hd : d ∣ L) : ZMod d →+ ZMod L :=
  ZMod.lift d ⟨scaledIntCast ((L / d : ℕ) : ZMod L), by
    change ((L / d : ℕ) : ZMod L) * ((d : ℤ) : ZMod L) = 0
    calc
      _ = ((L / d * d : ℕ) : ZMod L) := by
        rw [Int.cast_natCast, Nat.cast_mul]
      _ = 0 := by rw [Nat.div_mul_cancel hd, ZMod.natCast_self]⟩

theorem cyclicInclusion_int {L d : ℕ} (hd : d ∣ L) (x : ℤ) :
    cyclicInclusion hd (x : ZMod d) = ((L / d : ℕ) : ZMod L) * (x : ZMod L) := by
  unfold cyclicInclusion
  exact ZMod.lift_coe d _ x

theorem cyclicInclusion_injective {L d : ℕ} (hd : d ∣ L) (hL : 0 < L) (hdpos : 0 < d) :
    Function.Injective (cyclicInclusion hd) := by
  unfold cyclicInclusion
  rw [ZMod.lift_injective]
  intro x hx
  change ((L / d : ℕ) : ZMod L) * (x : ZMod L) = 0 at hx
  have hCast : ((((L / d : ℕ) : ℤ) * x : ℤ) : ZMod L) = 0 := by
    simpa only [Int.cast_mul, Int.cast_natCast] using hx
  have hDvd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hCast
  have hProduct : ((L / d : ℕ) : ℤ) * (d : ℤ) = (L : ℤ) := by
    simpa only [Nat.cast_mul] using
      congrArg (fun p : ℕ => (p : ℤ)) (Nat.div_mul_cancel hd)
  rw [← hProduct] at hDvd
  have hQuotient : ((L / d : ℕ) : ℤ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd hL hd) hdpos))
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd x d).mpr
    ((Int.mul_dvd_mul_iff_left hQuotient).mp hDvd)

/-- The residue-group overlap differential printed in Theorem 3.23. -/
def lcmInclusionDifference (m n : ℕ) : (ZMod m × ZMod n) →+ ZMod (m.lcm n) :=
  (cyclicInclusion (Nat.dvd_lcm_left m n)).comp (AddMonoidHom.fst _ _) -
    (cyclicInclusion (Nat.dvd_lcm_right m n)).comp (AddMonoidHom.snd _ _)

theorem lcmInclusionDifference_surjective (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    Function.Surjective (lcmInclusionDifference m n) := by
  let L := m.lcm n
  let a := L / m
  let b := L / n
  have hCoprime : Nat.gcd a b = 1 := gcd_lcm_quotients m n hm hn
  have hBezout : (a : ZMod L) * (Nat.gcdA a b : ZMod L) +
      (b : ZMod L) * (Nat.gcdB a b : ZMod L) = 1 := by
    have h := congrArg (fun t : ℤ => (t : ZMod L)) (Nat.gcd_eq_gcd_ab a b)
    rw [hCoprime] at h
    simpa only [Int.cast_natCast, Int.cast_one, Nat.cast_one, Int.cast_add, Int.cast_mul] using h.symm
  have hValue (u v : ℤ) :
      lcmInclusionDifference m n ((u : ZMod m), (v : ZMod n)) =
        (a : ZMod L) * (u : ZMod L) - (b : ZMod L) * (v : ZMod L) := by
    change cyclicInclusion (Nat.dvd_lcm_left m n) (u : ZMod m) -
      cyclicInclusion (Nat.dvd_lcm_right m n) (v : ZMod n) = _
    rw [cyclicInclusion_int, cyclicInclusion_int]
  intro z
  obtain ⟨x, rfl⟩ := ZMod.intCast_surjective (n := L) z
  refine ⟨(((Nat.gcdA a b * x : ℤ) : ZMod m),
      ((-(Nat.gcdB a b) * x : ℤ) : ZMod n)), ?_⟩
  rw [hValue, Int.cast_mul, Int.cast_mul, Int.cast_neg]
  calc
    _ = ((a : ZMod L) * (Nat.gcdA a b : ZMod L) +
      (b : ZMod L) * (Nat.gcdB a b : ZMod L)) * (x : ZMod L) := by ring
    _ = (x : ZMod L) := by rw [hBezout, one_mul]

theorem paper4_lcmInclusionCokernel_subsingleton (m n : ℕ)
    (hm : 0 < m) (hn : 0 < n) :
    Subsingleton (ZMod (m.lcm n) ⧸ (lcmInclusionDifference m n).range) := by
  have hTop := AddMonoidHom.range_eq_top.mpr (lcmInclusionDifference_surjective m n hm hn)
  rw [hTop]
  exact QuotientAddGroup.subsingleton_quotient_top

/-- The printed identification fails for every pair with nontrivial gcd. -/
theorem paper4_no_lcmInclusionCokernel_equiv_gcd (m n : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hg : 1 < m.gcd n) :
    ¬ Nonempty ((ZMod (m.lcm n) ⧸ (lcmInclusionDifference m n).range) ≃
      ZMod (m.gcd n)) := by
  letI := paper4_lcmInclusionCokernel_subsingleton m n hm hn
  haveI : Fact (1 < m.gcd n) := ⟨hg⟩
  rintro ⟨e⟩
  exact zero_ne_one (e.symm.injective (Subsingleton.elim (e.symm 0) (e.symm 1)))

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``cyclicInclusion_int, ``cyclicInclusion_injective, ``lcmInclusionDifference_surjective,
      ``paper4_lcmInclusionCokernel_subsingleton,
      ``paper4_no_lcmInclusionCokernel_equiv_gcd] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"

end ManuscriptAudit.CyclicInclusionCokernel
