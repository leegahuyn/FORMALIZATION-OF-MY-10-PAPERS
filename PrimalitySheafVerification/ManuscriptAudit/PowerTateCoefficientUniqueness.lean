import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.PowerTateLinearCombination

/-! Uniqueness of two rotation coefficients can be checked at the native finite levels. -/

namespace ManuscriptAudit.PowerTateCoefficientUniqueness

open PowerTorsionTower PowerTateModule PowerTateLinearCombination

noncomputable section

variable (l : ℕ) [Fact l.Prime] (G : Type*) [AddCommGroup G]
variable (f r : AddMonoid.End G)

theorem level_form_of_adic (n : ℕ) (hE : Function.Surjective (evaluate l G n))
    (a b : ℤ_[l]) (he : endMap l f = a • 1 + b • endMap l r) :
    LevelForm l G f r n (PadicInt.toZModPow n a, PadicInt.toZModPow n b) := by
  unfold LevelForm
  apply LinearMap.ext
  intro P
  obtain ⟨x, rfl⟩ := hE P
  have h := congrArg (fun T : Module.End ℤ_[l] (Tate l G) => evaluate l G n (T x)) he
  change evaluate l G n (endMap l f x) = evaluate l G n (a • x + b • endMap l r x) at h
  rw [evaluate_endMap, map_add, evaluate_smul, evaluate_smul, evaluate_endMap] at h
  exact h

private theorem residue_ext {a b : ℤ_[l]}
    (h : ∀ n, PadicInt.toZModPow (n + 1) a = PadicInt.toZModPow (n + 1) b) : a = b := by
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  cases n with
  | zero =>
    letI : Subsingleton (ZMod (l ^ 0)) := by simpa only [pow_zero] using (inferInstance : Subsingleton (ZMod 1))
    exact Subsingleton.elim _ _
  | succ n => exact h n

theorem exists_unique_adic_form
    (h : ∀ n, ∃! ab, LevelForm l G f r (n + 1) ab)
    (hTrans : ∀ n, Function.Surjective (transition l G n))
    (hEval : ∀ n, Function.Surjective (evaluate l G n)) :
    ∃! ab : ℤ_[l] × ℤ_[l], endMap l f = ab.1 • 1 + ab.2 • endMap l r := by
  obtain ⟨a, b, hEq, hLevels⟩ := exists_adic_form l G f r h hTrans
  refine ⟨(a, b), hEq, ?_⟩
  intro cd hCD
  have hReduction (n : ℕ) :
      (PadicInt.toZModPow (n + 1) cd.1, PadicInt.toZModPow (n + 1) cd.2) =
        (PadicInt.toZModPow (n + 1) a, PadicInt.toZModPow (n + 1) b) := by
    obtain ⟨ab, _, hUnique⟩ := h n
    have hCD' := level_form_of_adic l G f r (n + 1) (hEval (n + 1)) cd.1 cd.2 hCD
    exact (hUnique _ hCD').trans (hUnique _ (hLevels n)).symm
  exact Prod.ext
    (residue_ext l fun n => congrArg Prod.fst (hReduction n))
    (residue_ext l fun n => congrArg Prod.snd (hReduction n))

end
end ManuscriptAudit.PowerTateCoefficientUniqueness

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.PowerTateCoefficientUniqueness.level_form_of_adic,
      ``ManuscriptAudit.PowerTateCoefficientUniqueness.exists_unique_adic_form] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
