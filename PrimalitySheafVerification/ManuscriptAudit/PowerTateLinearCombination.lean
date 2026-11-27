import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.PowerTateModule

/-! Unique finite scalar coordinates lift through the actual prime-adic inverse limit. -/

namespace ManuscriptAudit.PowerTateLinearCombination

open TorsionFrobeniusModule PowerTorsionTower PowerTateModule

noncomputable section

variable (l : ℕ) [Fact l.Prime] (G : Type*) [AddCommGroup G]
variable (f r : AddMonoid.End G)

def LevelForm (n : ℕ) (ab : ZMod (l ^ n) × ZMod (l ^ n)) : Prop :=
  mapLinear (l ^ n) f = ab.1 • 1 + ab.2 • mapLinear (l ^ n) r

variable (h : ∀ n, ∃! ab, LevelForm l G f r (n + 1) ab)

private def coefficient : (n : ℕ) → ZMod (l ^ n) × ZMod (l ^ n)
  | 0 => (0, 0)
  | n + 1 => Classical.choose (h n)

private theorem coefficient_form (n : ℕ) : LevelForm l G f r (n + 1) (coefficient l G f r h (n + 1)) :=
  (Classical.choose_spec (h n)).1

private theorem coefficient_compatible
    (hTrans : ∀ n, Function.Surjective (transition l G n)) (n : ℕ) :
    let reduce := PadicResidueSystems.reduction l (Nat.le_succ n)
    (reduce (coefficient l G f r h (n + 1)).1,
      reduce (coefficient l G f r h (n + 1)).2) = coefficient l G f r h n := by
  cases n with
  | zero => exact Subsingleton.elim _ _
  | succ n =>
    let reduce := PadicResidueSystems.reduction l (Nat.le_succ (n + 1))
    let c := coefficient l G f r h (n + 2)
    have hLevel : LevelForm l G f r (n + 1) (reduce c.1, reduce c.2) := by
      apply LinearMap.ext
      intro x
      obtain ⟨y, rfl⟩ := hTrans (n + 1) x
      let T := transition l G (n + 1)
      change mapLinear (l ^ (n + 1)) f (T y) =
        reduce c.1 • T y + reduce c.2 • mapLinear (l ^ (n + 1)) r (T y)
      calc
        _ = T (mapLinear (l ^ (n + 2)) f y) := (map_transition l f (n + 1) y).symm
        _ = T (c.1 • y + c.2 • mapLinear (l ^ (n + 2)) r y) :=
          congrArg T (congrArg (fun F : Module.End (ZMod (l ^ (n + 2))) _ => F y)
            (coefficient_form l G f r h (n + 1)))
        _ = _ := by
          change transition l G (n + 1) (c.1 • y + c.2 • mapAdd (l ^ (n + 2)) r y) =
            reduce c.1 • transition l G (n + 1) y +
              reduce c.2 • mapAdd (l ^ (n + 1)) r (transition l G (n + 1) y)
          rw [map_add, transition_smul l G (Fact.out : l.Prime).ne_zero,
            transition_smul l G (Fact.out : l.Prime).ne_zero, map_transition]
    exact (Classical.choose_spec (h n)).2 _ hLevel

include h in
/-- Coefficients from actual finite-level linear maps determine the compatible prime-adic form. -/
theorem exists_adic_form (hTrans : ∀ n, Function.Surjective (transition l G n)) :
    ∃ a b : ℤ_[l], (endMap l f = a • 1 + b • endMap l r) ∧
      ∀ n, LevelForm l G f r (n + 1) (PadicInt.toZModPow (n + 1) a, PadicInt.toZModPow (n + 1) b) := by
  let c := coefficient l G f r h
  let s : PadicResidueSystems.systems l := ⟨fun n => (c n).1,
    PadicResidueSystems.compatible_of_successors l _ fun n =>
      congrArg Prod.fst (coefficient_compatible l G f r h hTrans n)⟩
  let t : PadicResidueSystems.systems l := ⟨fun n => (c n).2,
    PadicResidueSystems.compatible_of_successors l _ fun n =>
      congrArg Prod.snd (coefficient_compatible l G f r h hTrans n)⟩
  let e := PadicResidueSystems.padicRingEquiv l
  let a := e.symm s
  let b := e.symm t
  have ha (n : ℕ) : PadicInt.toZModPow n a = (c n).1 :=
    congrArg (PadicResidueSystems.evaluate l n) (e.apply_symm_apply s)
  have hb (n : ℕ) : PadicInt.toZModPow n b = (c n).2 :=
    congrArg (PadicResidueSystems.evaluate l n) (e.apply_symm_apply t)
  have hf (n : ℕ) : LevelForm l G f r (n + 1)
      (PadicInt.toZModPow (n + 1) a, PadicInt.toZModPow (n + 1) b) := by
    rw [ha, hb]
    exact coefficient_form l G f r h n
  refine ⟨a, b, ?_, hf⟩
  apply LinearMap.ext
  intro x
  apply PowerTateModule.ext l G
  intro n
  cases n with
  | zero =>
    apply Subtype.ext
    have eq_zero (P : PowerTorsion l G 0) : (P : G) = 0 := by
      simpa only [pow_zero, one_nsmul] using (mem_iff (l ^ 0) G _).mp P.property
    exact (eq_zero _).trans (eq_zero _).symm
  | succ n =>
    change evaluate l G (n + 1) (endMap l f x) =
      evaluate l G (n + 1) (a • x + b • endMap l r x)
    rw [evaluate_endMap, map_add, evaluate_smul, evaluate_smul, evaluate_endMap]
    exact congrArg (fun F : Module.End (ZMod (l ^ (n + 1))) _ => F (evaluate l G (n + 1) x)) (hf n)

end
end ManuscriptAudit.PowerTateLinearCombination

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.PowerTateLinearCombination.exists_adic_form
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
