import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.MonotoneCofinalFactors
import PrimalitySheafVerification.ManuscriptAudit.PowerTorsionTailCard

/-! Cofinal exact torsion counts determine the whole native additive tower. -/

namespace ManuscriptAudit.PowerTorsionCofinalCard

open TorsionFrobeniusModule PowerTorsionTower PowerTorsionTailCard MonotoneCofinalFactors

noncomputable section

variable (l : ℕ) (G : Type*) [AddCommGroup G]

/-- It suffices to establish the square-order count at arbitrarily high exact levels. -/
theorem card_and_surjective_of_cofinal_exact {d : ℕ} (hd : 0 < d)
    (hCofinal : ∀ n, ∃ m, n ≤ m ∧ Nat.card (PowerTorsion l G m) = d ^ m) :
    (∀ n, Nat.card (PowerTorsion l G n) = d ^ n) ∧
      ∀ n, Function.Surjective (transition l G n) := by
  obtain ⟨m, hm, hM⟩ := hCofinal 1
  haveI : Finite (PowerTorsion l G m) := Nat.finite_of_card_ne_zero (by
    rw [hM]
    exact pow_ne_zero _ hd.ne')
  let e (P : Torsion l G) : PowerTorsion l G m := by
    refine ⟨P.val, (mem_iff (l ^ m) G P.val).mpr ?_⟩
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hm
    have hP := (mem_iff l G P.val).mp P.property
    rw [hk, pow_add, pow_one, mul_nsmul, hP, nsmul_zero]
  haveI : Finite (Torsion l G) := Finite.of_injective e (fun _ _ h =>
    Subtype.ext (congrArg (fun P : PowerTorsion l G m => P.val) h))
  have h0 : Nat.card (PowerTorsion l G 0) = 1 := by
    letI : Unique (PowerTorsion l G 0) := ⟨⟨0⟩, fun P => Subtype.ext (by
      change (P : G) = 0
      simpa only [pow_zero, one_nsmul] using (mem_iff (l ^ 0) G _).mp P.property)⟩
    exact Nat.card_unique
  have hMono : Antitone (fun n => Nat.card (scaleToFirst l G n).range) := by
    apply antitone_nat_of_succ_le
    intro n
    let f (P : (scaleToFirst l G (n + 1)).range) : (scaleToFirst l G n).range :=
      ⟨P.val, range_scaleToFirst_decreasing l G n P.property⟩
    exact Nat.card_le_card_of_injective f (fun _ _ h =>
      Subtype.ext (congrArg (fun P : (scaleToFirst l G n).range => (P : Torsion l G)) h))
  have hAll := (exact_of_cofinal_exact
    (fun n => Nat.card (scaleToFirst l G n).range) (fun n => Nat.card (PowerTorsion l G n))
    hd h0 (level_card_factor l G) hMono hCofinal).2
  exact card_and_surjective_of_eventually_exact l G (N := 0) hd (fun n _ => hAll n)

end
end ManuscriptAudit.PowerTorsionCofinalCard

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.PowerTorsionCofinalCard.card_and_surjective_of_cofinal_exact
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
