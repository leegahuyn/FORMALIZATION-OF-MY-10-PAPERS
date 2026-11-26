import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Cokernels after pushing out a monomorphism

Pushing the first arrow of a short exact sequence along any map keeps
its quotient. The map from the pushout to the same quotient is a
canonical cokernel of the new inclusion.
-/

namespace ManuscriptAudit.CokernelPushout

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {C : Type*} [Category* C] [Abelian C]
variable {A B D : C} (f : A ⟶ B) (r : A ⟶ D)

private def projection : pushout f r ⟶ cokernel f :=
  pushout.desc (cokernel.π f) 0 (by simp)

@[reassoc (attr := simp)]
private theorem inl_projection :
    pushout.inl f r ≫ projection f r = cokernel.π f := by
  simp [projection]

@[reassoc (attr := simp)]
/-- The new inclusion is killed by the projection to the original cokernel. -/
theorem inr_projection : pushout.inr f r ≫ projection f r = 0 := by
  simp [projection]

private theorem projection_epi : Epi (projection f r) := by
  refine ⟨fun {_} a b h ↦ ?_⟩
  apply (cancel_epi (cokernel.π f)).mp
  simpa only [Category.assoc, inl_projection] using
    congrArg (fun k ↦ pushout.inl f r ≫ k) h

private def projectionIsCokernel :
    IsColimit (CokernelCofork.ofπ (projection f r) (inr_projection f r)) := by
  letI := projection_epi f r
  apply CokernelCofork.IsColimit.ofπ'
  intro W k hk
  have h : f ≫ (pushout.inl f r ≫ k) = 0 := by
    rw [← Category.assoc, pushout.condition, Category.assoc, hk, comp_zero]
  refine ⟨cokernel.desc f (pushout.inl f r ≫ k) h, ?_⟩
  apply pushout.hom_ext
  · rw [inl_projection_assoc, cokernel.π_desc]
  · rw [inr_projection_assoc, zero_comp, hk]

/-- The native short complex obtained by pushing out the first arrow. -/
def sequence : ShortComplex C :=
  ShortComplex.mk (pushout.inr f r) (projection f r) (inr_projection f r)

/-- The pushed-out sequence is short exact whenever the original arrow is monic. -/
theorem sequence_shortExact [Mono f] : (sequence f r).ShortExact := by
  have hMono : Mono (pushout.inr f r) := inferInstance
  exact ShortComplex.ShortExact.mk'
    ((sequence f r).exact_of_g_is_cokernel (projectionIsCokernel f r))
    hMono (projection_epi f r)

/-- The inclusion of the original middle object still has its original image in the quotient. -/
theorem inl_sequence_g : pushout.inl f r ≫ (sequence f r).g = cokernel.π f :=
  inl_projection f r

end

end ManuscriptAudit.CokernelPushout

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CokernelPushout.sequence_shortExact,
      ``ManuscriptAudit.CokernelPushout.inl_sequence_g] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
