import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.FourTorsionDeterminantTools
import PrimalitySheafVerification.ManuscriptAudit.TorsionFrobeniusModule

/-! Finite group order and a lower torsion bound detect higher two-power points. -/

namespace ManuscriptAudit.HigherTwoPowerFixedCard

open TorsionFrobeniusModule WeierstrassFrobeniusModTwo

noncomputable section

variable {H V : Type*} [AddCommGroup H] [Finite H] [AddCommGroup V]

/-- Some point is killed by twice the given multiple when the given kernel is too small. -/
theorem exists_higher_torsion (k r : ℕ) (hCard : 2 ^ r ∣ Nat.card H)
    (hKer : Nat.card (Torsion k H) < 2 ^ r) :
    ∃ P : H, (2 * k : ℕ) • P = 0 ∧ k • P ≠ 0 := by
  let f : H →+ H := nsmulAddMonoidHom k
  have hCard' : Nat.card H = Nat.card f.range * Nat.card f.ker := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker,
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv]
  have hEven : 2 ∣ Nat.card f.range := by
    by_contra hOdd
    have hCoprime : (2 ^ r : ℕ).Coprime (Nat.card f.range) :=
      ((Nat.prime_two.coprime_iff_not_dvd).mpr hOdd).pow_left r
    have hd : 2 ^ r ∣ Nat.card f.ker := hCoprime.dvd_of_dvd_mul_left (by rwa [← hCard'])
    have hle : 2 ^ r ≤ Nat.card f.ker := Nat.le_of_dvd Nat.card_pos hd
    exact (not_le_of_gt hKer) hle
  obtain ⟨Q, hQ₀, hQ₂⟩ := (two_dvd_card_iff_nonzero_two_torsion (↥f.range)).mp hEven
  obtain ⟨P, hP⟩ := Q.property
  change k • P = (Q : H) at hP
  refine ⟨P, ?_, ?_⟩
  · rw [mul_nsmul', hP]
    exact congrArg (fun x : ↥f.range => (x : H)) hQ₂
  · rw [hP]
    exact fun h => hQ₀ (Subtype.ext h)

/-- A bijective inclusion of the torsion subgroup gives the divisibility of the group order. -/
theorem card_dvd_of_torsion_bijective (m : ℕ) (j : Torsion m H →+ V)
    (hj : Function.Bijective j) : Nat.card V ∣ Nat.card H := by
  have hT := Nat.card_congr (Equiv.ofBijective j hj)
  have h := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (subgroup m H)
  change Nat.card H = Nat.card (H ⧸ subgroup m H) * Nat.card (Torsion m H) at h
  rw [hT] at h
  exact ⟨Nat.card (H ⧸ subgroup m H), h.trans (Nat.mul_comm _ _)⟩

/-- Multiplication by one more than the smaller exponent moves a point of higher torsion. -/
theorem exists_image_moved (k r : ℕ) (hCard : 2 ^ r ∣ Nat.card H)
    (hKer : Nat.card (Torsion k H) < 2 ^ r)
    (j : Torsion (2 * k) H →+ V) (hj : Function.Injective j) :
    ∃ P : Torsion (2 * k) H, (k + 1) • j P ≠ j P := by
  obtain ⟨P, hP, hPn⟩ := exists_higher_torsion k r hCard hKer
  let Q : Torsion (2 * k) H := ⟨P, hP⟩
  refine ⟨Q, ?_⟩
  intro he
  rw [add_nsmul, one_nsmul] at he
  have hZero : k • j Q = 0 := add_right_cancel (he.trans (zero_add _).symm)
  have hz : k • Q = 0 := hj (by rw [map_nsmul, map_zero, hZero])
  exact hPn (congrArg (fun x : Torsion (2 * k) H => (x : H)) hz)

end
end ManuscriptAudit.HigherTwoPowerFixedCard

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.HigherTwoPowerFixedCard.exists_higher_torsion,
      ``ManuscriptAudit.HigherTwoPowerFixedCard.card_dvd_of_torsion_bijective,
      ``ManuscriptAudit.HigherTwoPowerFixedCard.exists_image_moved] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
