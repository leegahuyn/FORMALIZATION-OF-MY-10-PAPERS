import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.KernelImageHOne
import PrimalitySheafVerification.ManuscriptAudit.ProetaleContinuousDirectImageGlobal
import PrimalitySheafVerification.ManuscriptAudit.ProetaleClosedKernelLocalSupport

/-! For a field-valued closed point, restriction of the actual continuous
adic global sections is surjective and the support-kernel map in H¹ is injective. -/

namespace ManuscriptAudit.ProetaleClosedAdicHOne

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open ProetaleContinuousDirectImageMaps (functions functionsOver diagonal)
open ProetaleContinuousDirectImageGlobal (HZeroEquiv terminalEquiv)
open ProetaleClosedKernelLocalSupport (K inc)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{0}} (L : Type) [Field L]
variable (i : Spec (CommRingCat.of L) ⟶ X) [IsClosedImmersion i]
variable (ℓ : ℕ) [Fact ℓ.Prime]

private abbrev M := ℤ_[ℓ]
private abbrev A := AddCommGrpCat.{1}
private abbrev integers :=
  (constantSheaf (Scheme.ProEt.topology X) A).obj (AddCommGrpCat.of (ULift.{1} ℤ))

theorem restriction_HZero_surjective :
    Function.Surjective (Sheaf.H.map (diagonal (M ℓ) i) 0) := by
  let hT := MorphismProperty.Over.mkIdTerminal @WeaklyEtale X
  let e := HZeroEquiv (M ℓ) i
  let u := Sheaf.H.equiv₀ (functions (M ℓ) X) hT
  intro x
  let y := e x (IsLocalRing.closedPoint L)
  refine ⟨u.symm ⟨ContinuousMap.const X y⟩, e.injective ?_⟩
  apply ContinuousMap.ext
  intro z
  change terminalEquiv (M ℓ) i ((Sheaf.H.equiv₀ (functionsOver (M ℓ) i) hT)
    (Sheaf.H.map (diagonal (M ℓ) i) 0 (u.symm ⟨ContinuousMap.const X y⟩))) z = e x z
  rw [← Sheaf.H.equiv₀_naturality, AddEquiv.apply_symm_apply]
  change e x (IsLocalRing.closedPoint L) = e x z
  exact congrArg (e x) (Subsingleton.elim _ _)

private theorem hom_postcomp_surjective :
    Function.Surjective (fun a : integers (X := X) ⟶ functions (M ℓ) X ↦
      a ≫ diagonal (M ℓ) i) := by
  intro b
  obtain ⟨a, ha⟩ := restriction_HZero_surjective L i ℓ (Ext.mk₀ b)
  refine ⟨Ext.addEquiv₀ a, ?_⟩
  apply Ext.addEquiv₀.symm.injective
  change Ext.mk₀ (Ext.addEquiv₀ a ≫ diagonal (M ℓ) i) = Ext.mk₀ b
  rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_addEquiv₀_apply]
  exact ha

theorem kernel_HOne_injective :
    Function.Injective (Sheaf.H.map (inc i (M ℓ)) 1) :=
  KernelImageHOne.one_postcomp_injective (diagonal (M ℓ) i) integers (hom_postcomp_surjective L i ℓ)

end

end ManuscriptAudit.ProetaleClosedAdicHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleClosedAdicHOne.restriction_HZero_surjective,
      ``ManuscriptAudit.ProetaleClosedAdicHOne.kernel_HOne_injective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
