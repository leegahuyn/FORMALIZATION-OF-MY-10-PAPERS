import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Exact

/-! Pushing out the left object of an exact extension keeps the same
right object and gives a short exact extension by the new kernel. -/

namespace ManuscriptAudit.PushoutShortExact

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {C : Type*} [Category* C] [Abelian C]
variable (S : ShortComplex C) {F : C} (u : S.X₁ ⟶ F)

private theorem pushout_condition_zero : S.f ≫ S.g = u ≫ (0 : F ⟶ S.X₃) := by
  rw [S.zero, comp_zero]

abbrev quotientProjection : pushout S.f u ⟶ S.X₃ :=
  pushout.desc S.g 0 (pushout_condition_zero S u)

@[reassoc (attr := simp)]
theorem inl_quotientProjection :
    pushout.inl S.f u ≫ quotientProjection S u = S.g :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem inr_quotientProjection :
    pushout.inr S.f u ≫ quotientProjection S u = 0 :=
  pushout.inr_desc _ _ _

/-- The native short complex obtained by pushing out the first arrow. -/
def pushKernel : ShortComplex C :=
  ShortComplex.mk (pushout.inr S.f u) (quotientProjection S u) (inr_quotientProjection S u)

def toPushKernel : S ⟶ pushKernel S u where
  τ₁ := u
  τ₂ := pushout.inl S.f u
  τ₃ := 𝟙 S.X₃
  comm₁₂ := (pushout.condition (f := S.f) (g := u)).symm
  comm₂₃ := by
    change pushout.inl S.f u ≫ quotientProjection S u = S.g ≫ 𝟙 S.X₃
    rw [inl_quotientProjection, Category.comp_id]

private theorem quotientProjection_epi (hS : S.ShortExact) : Epi (quotientProjection S u) := by
  letI : Epi S.g := hS.epi_g
  constructor
  intro Z f g h
  apply (cancel_epi S.g).mp
  rw [← inl_quotientProjection S u, Category.assoc, Category.assoc, h]

private def quotientProjection_isCokernel (hS : S.ShortExact) :
    IsColimit (CokernelCofork.ofπ (quotientProjection S u) (inr_quotientProjection S u)) := by
  letI := quotientProjection_epi S u hS
  refine CokernelCofork.IsColimit.ofπ' _ _ ?_
  intro Z k hk
  have hk' : S.f ≫ (pushout.inl S.f u ≫ k) = 0 := by
    rw [← Category.assoc, pushout.condition, Category.assoc, hk, comp_zero]
  obtain ⟨m, hm⟩ := CokernelCofork.IsColimit.desc' hS.gIsCokernel (pushout.inl S.f u ≫ k) hk'
  refine ⟨m, ?_⟩
  apply pushout.hom_ext
  · rw [← Category.assoc, inl_quotientProjection]
    exact hm
  · rw [← Category.assoc, inr_quotientProjection, zero_comp, hk]

/-- Pushout of the kernel of a short exact sequence is short exact. -/
theorem pushKernel_shortExact (hS : S.ShortExact) : (pushKernel S u).ShortExact := by
  letI : Mono S.f := hS.mono_f
  exact {
    exact := ShortComplex.exact_of_g_is_cokernel _ (quotientProjection_isCokernel S u hS)
    mono_f := Abelian.mono_pushout_of_mono_f _ _
    epi_g := quotientProjection_epi S u hS }

end
end ManuscriptAudit.PushoutShortExact

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.PushoutShortExact.pushKernel_shortExact
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
