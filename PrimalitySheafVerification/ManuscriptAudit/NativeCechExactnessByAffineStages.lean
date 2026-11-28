import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NativeCechNerve

/-! Exactness ascends through a genuine affine stage system whenever
sections have stage representatives and vanishing is detected at a stage. -/

namespace ManuscriptAudit.NativeCechExactnessByAffineStages

open CategoryTheory CategoryTheory.Limits
open NativeCechNerve (cochainExactAt_succ_iff)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {J : Type*} [Category* J]
  {D : J ⥤ CochainComplex AddCommGrpCat.{u} ℕ} (c : Cocone D)

set_option maxHeartbeats 3400000 in
/-- The two actual continuity properties suffice for exactness of the
literal cochain complex at the limit. -/
theorem exactAt_succ (n : ℕ)
    (hRep : ∀ x : c.pt.X (n + 1), ∃ (j : J) (z : (D.obj j).X (n + 1)),
      (c.ι.app j).f (n + 1) z = x)
    (hZero : ∀ (j : J) (z : (D.obj j).X (n + 2)), (c.ι.app j).f (n + 2) z = 0 →
      ∃ (k : J) (jk : j ⟶ k), (D.map jk).f (n + 2) z = 0)
    (hD : ∀ j, (D.obj j).ExactAt (n + 1)) :
    c.pt.ExactAt (n + 1) := by
  apply (cochainExactAt_succ_iff _ n).mpr
  intro x hx
  obtain ⟨j, z, hz⟩ := hRep x
  let w := (D.obj j).d (n + 1) (n + 2) z
  have hw : (c.ι.app j).f (n + 2) w = 0 := by
    have h := congrArg (fun g : (D.obj j).X (n + 1) ⟶ c.pt.X (n + 2) ↦ g z)
      ((c.ι.app j).comm (n + 1) (n + 2)).symm
    change (c.ι.app j).f (n + 2) w = c.pt.d (n + 1) (n + 2) ((c.ι.app j).f (n + 1) z) at h
    exact h.trans ((congrArg (c.pt.d (n + 1) (n + 2)) hz).trans hx)
  obtain ⟨k, jk, hk⟩ := hZero j w hw
  let y := (D.map jk).f (n + 1) z
  have hy : (D.obj k).d (n + 1) (n + 2) y = 0 := by
    have h := congrArg (fun g : (D.obj j).X (n + 1) ⟶ (D.obj k).X (n + 2) ↦ g z)
      ((D.map jk).comm (n + 1) (n + 2)).symm
    change (D.map jk).f (n + 2) w = (D.obj k).d (n + 1) (n + 2) y at h
    exact h.symm.trans hk
  obtain ⟨p, hp⟩ := (cochainExactAt_succ_iff _ n).mp (hD k) y hy
  refine ⟨(c.ι.app k).f n p, ?_⟩
  have h₁ := congrArg (fun g : (D.obj k).X n ⟶ c.pt.X (n + 1) ↦ g p)
    ((c.ι.app k).comm n (n + 1)).symm
  have h₂ := congrArg (fun g : (D.obj j) ⟶ c.pt ↦ (g.f (n + 1)) z) (c.w jk)
  change (c.ι.app k).f (n + 1) ((D.obj k).d n (n + 1) p) =
    c.pt.d n (n + 1) ((c.ι.app k).f n p) at h₁
  change (c.ι.app k).f (n + 1) y = (c.ι.app j).f (n + 1) z at h₂
  exact h₁.symm.trans ((congrArg ((c.ι.app k).f (n + 1)) hp).trans (h₂.trans hz))

end
end ManuscriptAudit.NativeCechExactnessByAffineStages

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NativeCechExactnessByAffineStages.exactAt_succ
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
