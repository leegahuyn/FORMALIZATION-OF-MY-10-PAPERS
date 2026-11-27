import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Sites.Abelian

/-! A short complex of sheaves that is short exact on every object
is short exact as a complex of sheaves. -/

namespace ManuscriptAudit.PointwiseSheafShortExact

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v w z

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {A : Type w} [Category.{z} A] [Abelian A] [HasSheafify J A]

private abbrev P := sheafToPresheaf J A

variable (S : ShortComplex (Sheaf J A))
variable (h : ∀ U : Cᵒᵖ, (S.map (P J ⋙ (evaluation Cᵒᵖ A).obj U)).ShortExact)

include h in
theorem shortExact : S.ShortExact := by
  haveI : Mono ((P J).map S.f) :=
    (NatTrans.mono_iff_mono_app _).2 (fun U ↦ (h U).mono_f)
  haveI : Epi ((P J).map S.g) :=
    (NatTrans.epi_iff_epi_app _).2 (fun U ↦ (h U).epi_g)
  have hm : Mono S.f := by
    constructor
    intro T g k hEq
    apply (P J).map_injective
    apply (cancel_mono ((P J).map S.f)).mp
    simpa only [← Functor.map_comp] using congrArg (fun f ↦ (P J).map f) hEq
  have he : Epi S.g := by
    constructor
    intro T g k hEq
    apply (P J).map_injective
    apply (cancel_epi ((P J).map S.g)).mp
    simpa only [← Functor.map_comp] using congrArg (fun f ↦ (P J).map f) hEq
  let c := KernelFork.ofι S.f S.zero
  have hc : IsLimit c := by
    apply isLimitOfReflects (P J)
    apply (KernelFork.isLimitMapConeEquiv c (P J)).symm
    apply evaluationJointlyReflectsLimits
    intro U
    apply (KernelFork.isLimitMapConeEquiv (c.map (P J)) ((evaluation Cᵒᵖ A).obj U)).symm
    exact (h U).fIsKernel
  exact ShortComplex.ShortExact.mk' (S.exact_of_f_is_kernel hc) hm he

end

end ManuscriptAudit.PointwiseSheafShortExact

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.PointwiseSheafShortExact.shortExact
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
