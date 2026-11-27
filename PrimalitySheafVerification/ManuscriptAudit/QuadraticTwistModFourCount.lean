import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import PrimalitySheafVerification.ManuscriptAudit.FourTorsionDeterminantTools
import PrimalitySheafVerification.ManuscriptAudit.TorsionFrobeniusModule

/-! Arithmetic determinant recovery from the two rational point groups of a quadratic twist pair. -/

namespace ManuscriptAudit.QuadraticTwistModFourCount

open TorsionFrobeniusModule FourTorsionDeterminantTools

private theorem torsion_card_dvd {G : Type*} [AddCommGroup G] (m : ℕ) :
    Nat.card (Torsion m G) ∣ Nat.card G := by
  refine ⟨Nat.card (G ⧸ subgroup m G), ?_⟩
  change Nat.card G = Nat.card ↥(subgroup m G) * Nat.card (G ⧸ subgroup m G)
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (subgroup m G), Nat.mul_comm]

/-- Four rational points at each of levels two and four force the whole group order to be
four modulo eight. -/
theorem card_mod_eight_of_torsion_four {G : Type*} [AddCommGroup G] [Finite G]
    (h₂ : Nat.card (Torsion 2 G) = 4) (h₄ : Nat.card (Torsion 4 G) = 4) :
    Nat.card G % 8 = 4 := by
  classical
  have h4 : 4 ∣ Nat.card G := h₂ ▸ torsion_card_dvd (G := G) 2
  have h8 : ¬ 8 ∣ Nat.card G := by
    intro hd
    obtain ⟨P, hP₄, hP₂⟩ := exists_orderFour hd h₂.le
    let j : Torsion 2 G → Torsion 4 G := fun Q =>
      ⟨Q.val, by
        have hQ : (2 : ℕ) • Q.val = 0 := Q.property
        change (4 : ℕ) • Q.val = 0
        rw [show (4 : ℕ) = 2 * 2 by decide, mul_nsmul', hQ, nsmul_zero]⟩
    have hj : Function.Injective j := by
      intro Q R h
      apply Subtype.ext
      exact congrArg (fun P : Torsion 4 G => P.val) h
    let P₄ : Torsion 4 G := ⟨P, hP₄⟩
    have hP : P₄ ∉ Set.range j := by
      rintro ⟨Q, hQ⟩
      have hQP : Q.val = P := congrArg (fun R : Torsion 4 G => R.val) hQ
      apply hP₂
      rw [← hQP]
      exact Q.property
    letI := Fintype.ofFinite (Torsion 2 G)
    letI := Fintype.ofFinite (Torsion 4 G)
    have hlt := Fintype.card_lt_of_injective_of_notMem j hj hP
    have hF₂ : Fintype.card (Torsion 2 G) = 4 := (Nat.card_eq_fintype_card).symm.trans h₂
    have hF₄ : Fintype.card (Torsion 4 G) = 4 := (Nat.card_eq_fintype_card).symm.trans h₄
    rw [hF₂, hF₄] at hlt
    omega
  omega

private theorem card_mod_eight_of_torsion_sixteen {G : Type*} [AddCommGroup G]
    (h : Nat.card (Torsion 4 G) = 16) : Nat.card G % 8 = 0 := by
  have h16 : 16 ∣ Nat.card G := h ▸ torsion_card_dvd (G := G) 4
  omega

/-- The 16/4 and 4/4 kernel patterns recover the residue of a finite-field size from the
complementary point counts of the two twist groups. -/
theorem determinant_eq_of_count_pair {G H : Type*}
    [AddCommGroup G] [AddCommGroup H] [Finite G] [Finite H]
    (q : ℕ) (d : ZMod 4)
    (h₂G : Nat.card (Torsion 2 G) = 4) (h₂H : Nat.card (Torsion 2 H) = 4)
    (hsum : Nat.card G + Nat.card H = 2 * (q + 1))
    (hpattern : (d = 1 ∧
      ((Nat.card (Torsion 4 G) = 16 ∧ Nat.card (Torsion 4 H) = 4) ∨
       (Nat.card (Torsion 4 G) = 4 ∧ Nat.card (Torsion 4 H) = 16))) ∨
      (d = 3 ∧ Nat.card (Torsion 4 G) = 4 ∧ Nat.card (Torsion 4 H) = 4)) :
    d = (q : ZMod 4) := by
  rcases hpattern with ⟨rfl, ⟨hG, hH⟩ | ⟨hG, hH⟩⟩ | ⟨rfl, hG, hH⟩
  · have hG' := card_mod_eight_of_torsion_sixteen hG
    have hH' := card_mod_eight_of_torsion_four h₂H hH
    exact (ZMod.natCast_eq_natCast_iff' 1 q 4).mpr (by omega)
  · have hG' := card_mod_eight_of_torsion_four h₂G hG
    have hH' := card_mod_eight_of_torsion_sixteen hH
    exact (ZMod.natCast_eq_natCast_iff' 1 q 4).mpr (by omega)
  · have hG' := card_mod_eight_of_torsion_four h₂G hG
    have hH' := card_mod_eight_of_torsion_four h₂H hH
    exact (ZMod.natCast_eq_natCast_iff' 3 q 4).mpr (by omega)

end ManuscriptAudit.QuadraticTwistModFourCount

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.QuadraticTwistModFourCount.card_mod_eight_of_torsion_four,
      ``ManuscriptAudit.QuadraticTwistModFourCount.determinant_eq_of_count_pair] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
