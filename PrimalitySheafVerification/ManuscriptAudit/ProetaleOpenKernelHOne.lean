import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.KernelImageHOne
import PrimalitySheafVerification.ManuscriptAudit.OpenProetaleExtension
import PrimalitySheafVerification.ManuscriptAudit.ProetaleCohomologyIso

/-! Global section surjectivity on an actual open controls H¹ of a
restricted kernel through its actual categorical image. -/

namespace ManuscriptAudit.ProetaleOpenKernelHOne

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open OpenProetaleExtension (restriction proetalePostcompose abelianExtensionByZeroAdjunction)
open ProetaleCohomologyIso (cohomologyIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]

private abbrev A := AddCommGrpCat.{1}
private abbrev J (Y : Scheme.{0}) := Scheme.ProEt.topology Y
private abbrev R := restriction j A

/-- The actual open object at which the restricted terminal sections are evaluated. -/
abbrev chart : X.ProEt := (proetalePostcompose j).obj (Scheme.ProEt.mk (𝟙 U))

/-- The restriction of a product with both factors zero on the open is zero. -/
theorem restrictionProduct_isZero (F G : Sheaf (J X) A)
    (hF : IsZero ((R j).obj F)) (hG : IsZero ((R j).obj G)) :
    IsZero ((R j).obj (F ⨯ G)) := by
  letI : (R j).IsRightAdjoint := (abelianExtensionByZeroAdjunction j).isRightAdjoint
  let e := PreservesLimitPair.iso (R j) F G
  have h : IsZero ((R j).obj F ⨯ (R j).obj G) := by
    rw [IsZero.iff_id_eq_zero]
    apply prod.hom_ext
    · exact hF.eq_of_tgt _ _
    · exact hG.eq_of_tgt _ _
  exact h.of_iso e

variable {F G : Sheaf (J X) A} (g : F ⟶ G)

private theorem HZero_surjective
    (h : Function.Surjective (g.hom.app (op (chart j)))) :
    Function.Surjective (Sheaf.H.map ((R j).map g) 0) := by
  let hT := MorphismProperty.Over.mkIdTerminal @WeaklyEtale U
  let a := Sheaf.H.equiv₀ ((R j).obj F) hT
  let b := Sheaf.H.equiv₀ ((R j).obj G) hT
  intro y
  obtain ⟨x, hx⟩ := h (b y)
  refine ⟨a.symm x, b.injective ?_⟩
  change Sheaf.H.equiv₀ ((R j).obj G) hT (Sheaf.H.map ((R j).map g) 0 (a.symm x)) = _
  rw [← Sheaf.H.equiv₀_naturality]
  change ((((R j).map g).hom.app (op (Scheme.ProEt.mk (𝟙 U)))) (a (a.symm x)) = _
  rw [a.apply_symm_apply]
  exact hx

private abbrev integers :=
  (constantSheaf (J U) A).obj (AddCommGrpCat.of (ULift.{1} ℤ))

private theorem hom_surjective
    (h : Function.Surjective (g.hom.app (op (chart j)))) :
    Function.Surjective (fun x : integers (U := U) ⟶ (R j).obj F ↦ x ≫ (R j).map g) := by
  intro b
  obtain ⟨a, ha⟩ := HZero_surjective j g h (Ext.mk₀ b)
  refine ⟨Ext.addEquiv₀ a, ?_⟩
  apply Ext.addEquiv₀.symm.injective
  change Ext.mk₀ (Ext.addEquiv₀ a ≫ (R j).map g) = Ext.mk₀ b
  rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_addEquiv₀_apply]
  exact ha

/-- When the restricted target is zero, the actual restricted kernel is the restricted domain. -/
def restrictionKernelIso (hZero : IsZero ((R j).obj G)) :
    (R j).obj (kernel g) ≅ (R j).obj F := by
  letI : (R j).IsRightAdjoint := (abelianExtensionByZeroAdjunction j).isRightAdjoint
  letI : (R j).Additive := (R j).additive_of_preserves_binary_products
  have h : (R j).map g = 0 := hZero.eq_of_tgt _ _
  letI := kernel.ι_of_zero h
  exact PreservesKernel.iso (R j) g ≪≫ asIso (kernel.ι ((R j).map g))

/-- On the actual open, the kernel's H¹ vanishes if the ambient H¹
vanishes and each terminal section lifts through the actual restricted map. -/
theorem kernel_HOne_subsingleton
    (hLift : Function.Surjective (g.hom.app (op (chart j))))
    (hAmbient : Subsingleton (Sheaf.H ((R j).obj F) 1)) :
    Subsingleton (Sheaf.H ((R j).obj (kernel g)) 1) := by
  letI : (R j).IsRightAdjoint := (abelianExtensionByZeroAdjunction j).isRightAdjoint
  letI : (R j).Additive := (R j).additive_of_preserves_binary_products
  let e := cohomologyIso (X := U) (PreservesKernel.iso (R j) g) 1
  let b := KernelImageHOne.one_postcomp_injective ((R j).map g) integers (hom_surjective j g hLift)
  exact ⟨fun x y ↦ e.injective (b (hAmbient.elim _ _))⟩

end

end ManuscriptAudit.ProetaleOpenKernelHOne

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleOpenKernelHOne.kernel_HOne_subsingleton
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
