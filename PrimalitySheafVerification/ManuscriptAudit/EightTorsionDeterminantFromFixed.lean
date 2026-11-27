import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EightTorsionCountCongruences
import PrimalitySheafVerification.ManuscriptAudit.HigherTwoPowerFixedCard
import PrimalitySheafVerification.ManuscriptAudit.PadicResidueSystems

/-! Two geometric torsion levels detect the native Frobenius determinant modulo eight. -/

namespace ManuscriptAudit.EightTorsionDeterminantFromFixed

open TorsionFrobeniusModule HigherTwoPowerFixedCard EightTorsionCountCongruences

noncomputable section

def reduceEightFour : ZMod 8 →+* ZMod 4 :=
  PadicResidueSystems.reduction 2 (m := 2) (n := 3) (by decide)

def reduceSixteenEight : ZMod 16 →+* ZMod 8 :=
  PadicResidueSystems.reduction 2 (m := 3) (n := 4) (by decide)

private theorem eight_cases_three : ∀ x : ZMod 8, reduceEightFour x = 3 → x = 3 ∨ x = 7 := by
  decide

private theorem eight_cases_one : ∀ x : ZMod 8, reduceEightFour x = 1 → x = 1 ∨ x = 5 := by
  decide

private theorem sixteen_square_of_eight_one : ∀ x : ZMod 16,
    reduceSixteenEight x = 1 → x ^ 2 = 1 := by decide

private theorem sixteen_square_of_eight_five : ∀ x : ZMod 16,
    reduceSixteenEight x = 5 → x ^ 2 = 9 := by decide

variable {H V : Type*} [AddCommGroup H] [Finite H] [AddCommGroup V]

private theorem cast_eight_eq (q r : ℕ) (h : q % 8 = r) :
    (q : ZMod 8) = (r : ZMod 8) := by rw [← ZMod.natCast_mod q 8, h]

/-- The quadratic fixed group distinguishes the two residues congruent to three modulo four. -/
theorem residue_of_quadratic_fixed [Module (ZMod 8) V] (q : ℕ) (hq : q % 4 = 3)
    (d : ZMod 8) (hd₄ : reduceEightFour d = 3)
    (hH : Nat.card H = (q + 1) ^ 2) (hV : Nat.card V = 64)
    (hKer : Nat.card (Torsion 4 H) ≤ 16)
    (j : Torsion 8 H →+ V) (hj : Function.Injective j)
    (F₂ : V → V) (hFix : ∀ v, F₂ v = v ↔ ∃ Q : Torsion 8 H, j Q = v)
    (hScalar : ∀ v, F₂ v = (-d) • v) : d = (q : ZMod 8) := by
  have hs : q % 8 = 3 ∨ q % 8 = 7 := by omega
  rcases eight_cases_three d hd₄ with hd | hd
  · have hq₈ : q % 8 = 3 := by
      rcases hs with h | h
      · exact h
      · have hD : (2 : ℕ) ^ 6 ∣ Nat.card H := by
          rw [hH]
          exact quadratic_dvd_of_seven q h
        have hSmall : Nat.card (Torsion 4 H) < (2 : ℕ) ^ 6 :=
          hKer.trans_lt (by decide)
        obtain ⟨P, hMove⟩ := exists_image_moved 4 6 hD hSmall j hj
        have hF := (hFix (j P)).mpr ⟨P, rfl⟩
        rw [hScalar, hd, show (-(3 : ZMod 8)) = ((5 : ℕ) : ZMod 8) by decide,
          Nat.cast_smul_eq_nsmul] at hF
        exact (hMove hF).elim
    exact hd.trans (cast_eight_eq q 3 hq₈).symm
  · have hq₈ : q % 8 = 7 := by
      rcases hs with h | h
      · have hSurj : Function.Surjective j := by
          intro v
          apply (hFix v).mp
          rw [hScalar, hd, show (-(7 : ZMod 8)) = 1 by decide, one_smul]
        have hD := card_dvd_of_torsion_bijective 8 j ⟨hj, hSurj⟩
        rw [hH, hV] at hD
        exact (quadratic_not_dvd_of_three q h hD).elim
      · exact h
    exact hd.trans (cast_eight_eq q 7 hq₈).symm

/-- The quartic fixed group distinguishes the two residues congruent to one modulo four. -/
theorem residue_of_quartic_fixed [Module (ZMod 16) V] (q : ℕ) (hq : q % 4 = 1)
    (d : ZMod 8) (D : ZMod 16) (hd₄ : reduceEightFour d = 1) (hD : reduceSixteenEight D = d)
    (hH : Nat.card H = (q ^ 2 - 1) ^ 2) (hV : Nat.card V = 256)
    (hKer : Nat.card (Torsion 8 H) ≤ 64)
    (j : Torsion 16 H →+ V) (hj : Function.Injective j)
    (F₄ : V → V) (hFix : ∀ v, F₄ v = v ↔ ∃ Q : Torsion 16 H, j Q = v)
    (hScalar : ∀ v, F₄ v = D ^ 2 • v) : d = (q : ZMod 8) := by
  have hs : q % 8 = 1 ∨ q % 8 = 5 := by omega
  rcases eight_cases_one d hd₄ with hd | hd
  · have hS : D ^ 2 = 1 := sixteen_square_of_eight_one D (hD.trans hd)
    have hq₈ : q % 8 = 1 := by
      rcases hs with h | h
      · exact h
      · have hSurj : Function.Surjective j := by
          intro v
          apply (hFix v).mp
          rw [hScalar, hS, one_smul]
        have hDiv := card_dvd_of_torsion_bijective 16 j ⟨hj, hSurj⟩
        rw [hH, hV] at hDiv
        exact (quartic_not_dvd_of_five q h hDiv).elim
    exact hd.trans (cast_eight_eq q 1 hq₈).symm
  · have hS : D ^ 2 = 9 := sixteen_square_of_eight_five D (hD.trans hd)
    have hq₈ : q % 8 = 5 := by
      rcases hs with h | h
      · have hDiv : (2 : ℕ) ^ 8 ∣ Nat.card H := by
          rw [hH]
          exact quartic_dvd_of_one q h
        have hSmall : Nat.card (Torsion 8 H) < (2 : ℕ) ^ 8 :=
          hKer.trans_lt (by decide)
        obtain ⟨P, hMove⟩ := exists_image_moved 8 8 hDiv hSmall j hj
        have hF := (hFix (j P)).mpr ⟨P, rfl⟩
        rw [hScalar, hS, show (9 : ZMod 16) = ((9 : ℕ) : ZMod 16) by rfl,
          Nat.cast_smul_eq_nsmul] at hF
        exact (hMove hF).elim
      · exact h
    exact hd.trans (cast_eight_eq q 5 hq₈).symm

end
end ManuscriptAudit.EightTorsionDeterminantFromFixed

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.EightTorsionDeterminantFromFixed.residue_of_quadratic_fixed,
      ``ManuscriptAudit.EightTorsionDeterminantFromFixed.residue_of_quartic_fixed] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
