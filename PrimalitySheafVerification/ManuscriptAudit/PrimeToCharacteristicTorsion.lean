import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AdditiveKernelComposition

/-! Prime-level torsion counts extend to every integer prime to a fixed characteristic. -/

namespace ManuscriptAudit.PrimeToCharacteristicTorsion

open AdditiveKernelComposition TorsionFrobeniusModule

variable (G : Type*) [AddCommGroup G] (p : ℕ) [Fact p.Prime]

theorem surjective_and_card
    (hPrime : ∀ l : ℕ, l.Prime → l ≠ p →
      Function.Surjective (nsmulAddMonoidHom l : G →+ G) ∧ Nat.card (Torsion l G) = l ^ 2)
    (n : ℕ) (hN : ¬ p ∣ n) :
    Function.Surjective (nsmulAddMonoidHom n : G →+ G) ∧ Nat.card (Torsion n G) = n ^ 2 := by
  revert hN
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hN
    by_cases hOne : n = 1
    · subst n
      have h₁ : (nsmulAddMonoidHom 1 : G →+ G) = AddMonoidHom.id G := by
        ext x
        exact one_nsmul x
      haveI : Unique (Torsion 1 G) := by
        refine ⟨⟨0⟩, fun x => Subtype.ext ?_⟩
        change (x : G) = 0
        have h := (mem_iff 1 G x).mp x.property
        simpa only [one_nsmul] using h
      rw [h₁]
      exact ⟨fun x => ⟨x, rfl⟩, by simp⟩
    obtain ⟨l, hl, hlN⟩ := Nat.exists_prime_and_dvd hOne
    obtain ⟨k, hK⟩ := hlN
    have hK₀ : 0 < k := by
      by_contra h
      have hk : k = 0 := by omega
      rw [hk, mul_zero] at hK
      exact hN (hK.symm ▸ dvd_zero p)
    have hKlt : k < n := by
      calc
        k = 1 * k := (one_mul k).symm
        _ < l * k := Nat.mul_lt_mul_of_pos_right hl.one_lt hK₀
        _ = n := hK.symm
    have hlp : l ≠ p := by
      rintro rfl
      exact hN ⟨k, hK⟩
    have hkp : ¬ p ∣ k := fun hd => hN (hK.symm ▸ dvd_mul_of_dvd_right hd l)
    obtain ⟨hsL, hcL⟩ := hPrime l hl hlp
    obtain ⟨hsK, hcK⟩ := ih k hKlt hkp
    let f : G →+ G := nsmulAddMonoidHom l
    let g : G →+ G := nsmulAddMonoidHom k
    have hComp : (nsmulAddMonoidHom n : G →+ G) = f.comp g := by
      apply AddMonoidHom.ext
      intro x
      change n • x = l • (k • x)
      rw [hK, mul_nsmul']
    constructor
    · rw [hComp]
      exact hsL.comp hsK
    · change Nat.card ↥((nsmulAddMonoidHom n : G →+ G).ker) = n ^ 2
      rw [hComp, card_ker_comp f g hsK]
      change Nat.card (Torsion l G) * Nat.card (Torsion k G) = n ^ 2
      rw [hcL, hcK, hK, mul_pow]

end ManuscriptAudit.PrimeToCharacteristicTorsion

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.PrimeToCharacteristicTorsion.surjective_and_card
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
