import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CokernelPushout

/-! Compare a cokernel sequence with the one obtained by pushing out
and then embedding the new middle object. -/

namespace ManuscriptAudit.CokernelPushout

open CategoryTheory CategoryTheory.Limits

universe u v

noncomputable section

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D M D' N : C} (i : D ⟶ M) (r : D ⟶ D') (k : pushout i r ⟶ N)

/-- The inclusion of the new first object into the enlarged middle object. -/
def enlargedInclusion : D' ⟶ N := pushout.inr i r ≫ k

private theorem enlarged_square :
    i ≫ (pushout.inl i r ≫ k) = r ≫ enlargedInclusion i r k := by
  change i ≫ pushout.inl i r ≫ k = r ≫ pushout.inr i r ≫ k
  simpa only [Category.assoc] using congrArg (fun f : D ⟶ pushout i r ↦ f ≫ k)
    (pushout.condition (f := i) (g := r))

/-- The induced map of actual cokernels. -/
def enlargedQuotientMap : cokernel i ⟶ cokernel (enlargedInclusion i r k) :=
  cokernel.desc i ((pushout.inl i r ≫ k) ≫ cokernel.π (enlargedInclusion i r k)) (by
    rw [← Category.assoc, enlarged_square, Category.assoc, cokernel.condition, comp_zero])

/-- Mapping the quotient of the pushed-out sequence into the new
cokernel agrees with projecting after the enlarged middle map. -/
theorem projection_enlargedQuotientMap :
    (sequence i r).g ≫ enlargedQuotientMap i r k =
      k ≫ cokernel.π (enlargedInclusion i r k) := by
  let q := (sequence i r).g
  let u := enlargedQuotientMap i r k
  let j := enlargedInclusion i r k
  let π := cokernel.π j
  apply pushout.hom_ext
  · change pushout.inl i r ≫ (q ≫ u) = pushout.inl i r ≫ (k ≫ π)
    calc
      _ = cokernel.π i ≫ u := by rw [← Category.assoc, inl_sequence_g]
      _ = (pushout.inl i r ≫ k) ≫ π := cokernel.π_desc _ _ _
      _ = _ := Category.assoc _ _ _
  · change pushout.inr i r ≫ (q ≫ u) = pushout.inr i r ≫ (k ≫ π)
    have h : pushout.inr i r ≫ q = 0 := (sequence i r).zero
    calc
      _ = 0 := by rw [← Category.assoc, h, zero_comp]
      _ = j ≫ π := (cokernel.condition j).symm
      _ = _ := Category.assoc _ _ _

/-- The commuting map from the original to the enlarged cokernel sequence. -/
def enlargedComparison :
    ShortComplex.cokernelSequence i ⟶ ShortComplex.cokernelSequence (enlargedInclusion i r k) where
  τ₁ := r
  τ₂ := pushout.inl i r ≫ k
  τ₃ := enlargedQuotientMap i r k
  comm₁₂ := (enlarged_square i r k).symm
  comm₂₃ := (cokernel.π_desc _ _ _).symm

end

end ManuscriptAudit.CokernelPushout

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CokernelPushout.projection_enlargedQuotientMap,
      ``ManuscriptAudit.CokernelPushout.enlargedComparison] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
