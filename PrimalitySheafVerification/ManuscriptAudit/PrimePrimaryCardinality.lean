import Lean.Util.CollectAxioms
import Mathlib.GroupTheory.PGroup
import PrimalitySheafVerification.ManuscriptAudit.PowerTorsionTower

/-! Prime-primary cardinality under an explicit finite-group annihilator. -/

namespace ManuscriptAudit.PrimePrimaryCardinality

open TorsionFrobeniusModule

noncomputable section

variable (G : Type*) [AddCommGroup G] [Finite G]
variable (l : ℕ) [Fact l.Prime]

/-- In a group of order M² killed by M = l^n d, with d prime to l, the l^n-torsion has order l^(2n). -/
theorem card_torsion_of_square_annihilator (n d : ℕ) (hd : ¬l ∣ d)
    (hAnn : ∀ P : G, (l ^ n * d) • P = 0) (hCard : Nat.card G = (l ^ n * d) ^ 2) :
    Nat.card (Torsion (l ^ n) G) = (l ^ 2) ^ n := by
  let f : G →+ G := nsmulAddMonoidHom (l ^ n)
  have hprod : Nat.card G = Nat.card f.range * Nat.card f.ker := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker,
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv]
  have hRangeAnn (P : f.range) : d • P = 0 := by
    obtain ⟨Q, hQ⟩ := P.property
    apply Subtype.ext
    change d • (P : G) = 0
    rw [← hQ]
    change d • ((l ^ n) • Q) = 0
    rw [← mul_nsmul, hAnn Q]
  have hRange : ¬l ∣ Nat.card f.range := by
    intro h
    have h' : l ∣ Nat.card (Multiplicative f.range) :=
      (Nat.card_congr Multiplicative.ofAdd) ▸ h
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' l h'
    have hpow : x ^ d = 1 := hRangeAnn x.toAdd
    apply hd
    simpa only [hx] using orderOf_dvd_of_pow_eq_one hpow
  have hKernel : IsPGroup l (Multiplicative f.ker) := by
    intro P
    refine ⟨n, ?_⟩
    change (l ^ n) • P.toAdd = 0
    apply Subtype.ext
    exact AddMonoidHom.mem_ker.mp P.toAdd.property
  obtain ⟨k, hk'⟩ := IsPGroup.iff_card.mp hKernel
  have hk : Nat.card f.ker = l ^ k :=
    (Nat.card_congr Multiplicative.ofAdd).trans hk'
  have hG : Nat.card G = l ^ (n * 2) * d ^ 2 := by
    rw [hCard, mul_pow, pow_mul]
  have hl : l.Prime := Fact.out
  have hDvdK : l ^ k ∣ l ^ (n * 2) := by
    have hc := (((hl.coprime_iff_not_dvd).mpr hd).pow_left k).pow_right 2
    apply hc.dvd_of_dvd_mul_right
    rw [← hG, hprod, hk]
    exact dvd_mul_left _ _
  have hDvdG : l ^ (n * 2) ∣ l ^ k := by
    have hc := ((hl.coprime_iff_not_dvd).mpr hRange).pow_left (n * 2)
    apply hc.dvd_of_dvd_mul_left
    rw [← hk, ← hprod, hG]
    exact dvd_mul_right _ _
  change Nat.card f.ker = (l ^ 2) ^ n
  rw [hk, Nat.dvd_antisymm hDvdK hDvdG, ← pow_mul, Nat.mul_comm n 2]

end
end ManuscriptAudit.PrimePrimaryCardinality

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.PrimePrimaryCardinality.card_torsion_of_square_annihilator
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
