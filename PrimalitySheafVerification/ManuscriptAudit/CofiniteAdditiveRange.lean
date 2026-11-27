import Lean.Util.CollectAxioms
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Tactic.Abel

/-! A cofinite additive subgroup of an infinite group is the whole group. -/

namespace ManuscriptAudit.CofiniteAdditiveRange

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H] [Infinite H]

theorem surjective_of_finite_complement (f : G →+ H)
    (hFin : ((Set.range f)ᶜ).Finite) : Function.Surjective f := by
  intro h
  have hBad : ((Set.range f)ᶜ ∪ (h + ·) '' (Set.range f)ᶜ).Finite :=
    hFin.union (hFin.image (h + ·))
  obtain ⟨z, hz⟩ := hBad.exists_notMem
  have hz₁ : z ∈ Set.range f := by
    by_contra hn
    exact hz (Or.inl hn)
  have hz₂ : z - h ∈ Set.range f := by
    by_contra hn
    exact hz (Or.inr ⟨z - h, hn, by abel⟩)
  obtain ⟨x, hx⟩ := hz₁
  obtain ⟨y, hy⟩ := hz₂
  refine ⟨x - y, ?_⟩
  rw [map_sub, hx, hy]
  abel

end ManuscriptAudit.CofiniteAdditiveRange

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CofiniteAdditiveRange.surjective_of_finite_complement
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
