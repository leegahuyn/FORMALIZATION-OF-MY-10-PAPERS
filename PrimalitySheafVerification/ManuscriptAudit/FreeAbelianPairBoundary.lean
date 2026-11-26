import Lean.Util.CollectAxioms
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.Tactic.Abel

/-!
The free abelian pair and triple boundaries are exact at pairs.
They give the degree-one Čech relation for a single object.
-/

namespace ManuscriptAudit.FreeAbelianPairBoundary

open FreeAbelianGroup

universe u

variable (α : Type u)

def pairBoundary : FreeAbelianGroup (α × α) →+ FreeAbelianGroup α :=
  lift fun p => of p.2 - of p.1

def tripleBoundary : FreeAbelianGroup (α × α × α) →+ FreeAbelianGroup (α × α) :=
  lift fun p => of (p.2.1, p.2.2) - of (p.1, p.2.2) + of (p.1, p.2.1)

@[simp] theorem pairBoundary_of (x y : α) :
    pairBoundary α (of (x, y)) = of y - of x := lift_apply_of _ _

@[simp] theorem tripleBoundary_of (x y z : α) :
    tripleBoundary α (of (x, y, z)) = of (y, z) - of (x, z) + of (x, y) :=
  lift_apply_of _ _

theorem pairBoundary_comp_tripleBoundary : (pairBoundary α).comp (tripleBoundary α) = 0 := by
  apply lift_ext
  rintro ⟨x, y, z⟩
  simp only [AddMonoidHom.comp_apply, tripleBoundary_of, map_add, map_sub,
    pairBoundary_of, AddMonoidHom.zero_apply]
  abel

private def pairCone (a : α) : FreeAbelianGroup α →+ FreeAbelianGroup (α × α) :=
  lift fun x => of (a, x)

private def tripleCone (a : α) : FreeAbelianGroup (α × α) →+
    FreeAbelianGroup (α × α × α) :=
  lift fun x => of (a, x)

private theorem cone_identity (a : α) :
    (tripleBoundary α).comp (tripleCone α a) + (pairCone α a).comp (pairBoundary α) =
      AddMonoidHom.id (FreeAbelianGroup (α × α)) := by
  apply lift_ext
  rintro ⟨x, y⟩
  simp only [AddMonoidHom.add_apply, AddMonoidHom.comp_apply, AddMonoidHom.id_apply,
    tripleCone, pairCone, lift_apply_of, tripleBoundary_of, pairBoundary_of, map_sub]
  abel

theorem exists_tripleBoundary_of_pairBoundary_eq_zero (x : FreeAbelianGroup (α × α))
    (hx : pairBoundary α x = 0) : ∃ y, tripleBoundary α y = x := by
  cases isEmpty_or_nonempty α with
  | inl h =>
    have h0 : x = 0 := by
      induction x using FreeAbelianGroup.induction_on with
      | zero => rfl
      | of p => exact (h.false p.1).elim
      | neg p _ => exact (h.false p.1).elim
      | add a b ha hb => simp [ha, hb]
    exact ⟨0, by simp [h0]⟩
  | inr h =>
    let a := Classical.choice h
    refine ⟨tripleCone α a x, ?_⟩
    have hId := DFunLike.congr_fun (cone_identity α a) x
    simpa only [AddMonoidHom.add_apply, AddMonoidHom.comp_apply, AddMonoidHom.id_apply,
      hx, map_zero, add_zero] using hId

end ManuscriptAudit.FreeAbelianPairBoundary

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.FreeAbelianPairBoundary.pairBoundary_comp_tripleBoundary,
      ``ManuscriptAudit.FreeAbelianPairBoundary.exists_tripleBoundary_of_pairBoundary_eq_zero] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
