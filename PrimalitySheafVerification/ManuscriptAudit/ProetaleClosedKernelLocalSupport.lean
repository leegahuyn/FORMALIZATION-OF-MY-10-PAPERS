import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleClosedSupportLocalConstants
import PrimalitySheafVerification.ManuscriptAudit.SheafSectionDifference

/-! A kernel section of discrete closed restriction is locally
supported in the complementary open, or is locally zero. -/

namespace ManuscriptAudit.ProetaleClosedKernelLocalSupport

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleContinuousDirectImageMaps (functions functionsOver diagonal)
open ProetaleClosedSupportLocalConstants (openObject openArrow)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X Z Y : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i]
  (j : Y ⟶ X) [IsOpenImmersion j]
variable (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalAddGroup M]

abbrev K := kernel (diagonal M i)
abbrev inc : K i M ⟶ functions M X := kernel.ι (diagonal M i)

private theorem kernel_value_zero (U : X.ProEt) (s : (K i M).obj.obj (op U))
    (x : U.left) (hx : U.hom x ∈ Set.range i) :
    (show C(U.left, M) from ((inc i M).hom.app (op U) s).down) x = 0 := by
  obtain ⟨z, hz⟩ := hx
  obtain ⟨p, hp, _⟩ := Scheme.Pullback.exists_preimage_pullback (f := U.hom) (g := i) x z hz.symm
  have h := ConcreteCategory.congr_hom
    (congrArg (fun f : K i M ⟶ functionsOver M i ↦ f.hom.app (op U))
      (kernel.condition (diagonal M i))) s
  have h' := congrArg
    (fun f : ULift.{1} (C(↥(pullback U.hom i : Scheme.{0}), M)) ↦ f.down p) h
  change (show C(U.left, M) from ((inc i M).hom.app (op U) s).down)
    (pullback.fst U.hom i p) = 0 at h'
  rwa [hp] at h'

/-- Each point admits an ordinary open neighborhood on which the chart
factors through the complementary open or the kernel section is zero. -/
theorem locally_open_or_zero (hComplement : Set.range j = (Set.range i)ᶜ)
    (U : X.ProEt) (s : (K i M).obj.obj (op U)) (x : U.left) :
    ∃ W : U.left.Opens, x ∈ W ∧
      (Set.range (openObject U W).hom ⊆ Set.range j ∨
        (K i M).obj.map (openArrow U W).op s = 0) := by
  by_cases hx : U.hom x ∈ Set.range j
  · let V := U.hom ⁻¹ᵁ j.opensRange
    refine ⟨V, hx, Or.inl ?_⟩
    rintro _ ⟨a, rfl⟩
    change U.hom a.val ∈ Set.range j
    exact a.property
  · have hx' : U.hom x ∈ Set.range i := by
      by_contra h
      exact hx (hComplement.symm ▸ h)
    let f : C(U.left, M) := ((inc i M).hom.app (op U) s).down
    let V : U.left.Opens := ⟨f ⁻¹' {0}, (isOpen_discrete _).preimage f.continuous⟩
    have hxV : x ∈ V := kernel_value_zero i M U s x hx'
    refine ⟨V, hxV, Or.inr ?_⟩
    let g := openArrow U V
    apply SheafSectionDifference.section_injective (inc i M) (openObject U V)
    rw [NatTrans.naturality_apply (inc i M).hom g.op s, map_zero]
    apply ULift.ext
    apply ContinuousMap.ext
    intro a
    change f a.val = 0
    exact a.property

end
end ManuscriptAudit.ProetaleClosedKernelLocalSupport

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleClosedKernelLocalSupport.locally_open_or_zero
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
