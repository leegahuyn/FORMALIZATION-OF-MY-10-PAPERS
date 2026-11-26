import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import PrimalitySheafVerification.ManuscriptAudit.GeometricSkyscraperHZero
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleExtensionComposition

/-!
# Vanishing ordinary étale H¹ gives lifts over an open

Restriction is exact: it is both a left and a right adjoint. Thus
the restriction of a mono and its sheaf cokernel is a short exact
sequence, and zero degree-one cohomology of the restricted kernel
implies surjectivity on degree-zero sections.
-/

namespace ManuscriptAudit.OpenEtaleLocalLifts

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open OpenEtaleExtension

noncomputable section

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

private abbrev G := AddCommGrpCat.{u}
private abbrev R := restriction j G.{u}

/-- The actual restriction of a sheaf cokernel projection is surjective
on sections over the open when the restricted source has zero H¹. -/
theorem restrictedCokernel_sections_surjective
    {F I : Sheaf X.smallEtaleTopology G.{u}} (i : F ⟶ I) [Mono i]
    (hVanishing : Subsingleton (Sheaf.H ((R j).obj F) 1)) :
    Function.Surjective
      (((R j).map (cokernel.π i)).hom.app (op (Scheme.Etale.mk (𝟙 U)))) := by
  let RF := R j
  letI : RF.IsLeftAdjoint := (restrictionDirectImageAdjunction j).isLeftAdjoint
  letI : RF.IsRightAdjoint := (abelianExtensionByZeroAdjunction j).isRightAdjoint
  letI : RF.Additive := ⟨by intros; rfl⟩
  let Q := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
  have hQ : Q.ShortExact := {
    exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel i)
    mono_f := inferInstanceAs (Mono i)
    epi_g := inferInstanceAs (Epi (cokernel.π i)) }
  let QQ := Q.map RF
  have hQQ : QQ.ShortExact := hQ.map_of_exact RF
  let W := Scheme.Etale.mk (𝟙 U)
  let hW : IsTerminal W := MorphismProperty.Over.mkIdTerminal @Etale U
  let T := (constantSheaf U.smallEtaleTopology G.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  intro x
  let x₀ : Sheaf.H QQ.X₃ 0 := (Sheaf.H.equiv₀ QQ.X₃ hW).symm x
  have hh : (hQQ.extClass.postcomp T (show 0 + 1 = 1 by rfl)) x₀ = 0 :=
    hVanishing.allEq _ _
  have hExact := Ext.covariant_sequence_exact₃' T hQQ 0 1 rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at hExact
  obtain ⟨y, hy⟩ := (hExact x₀).mp hh
  refine ⟨Sheaf.H.equiv₀ QQ.X₂ hW y, ?_⟩
  change QQ.g.hom.app (op W) (Sheaf.H.equiv₀ QQ.X₂ hW y) = x
  change Sheaf.H.map QQ.g 0 y = x₀ at hy
  rw [Sheaf.H.equiv₀_naturality, hy]
  exact (Sheaf.H.equiv₀ QQ.X₃ hW).apply_symm_apply x

end

end ManuscriptAudit.OpenEtaleLocalLifts

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.OpenEtaleLocalLifts.restrictedCokernel_sections_surjective
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
