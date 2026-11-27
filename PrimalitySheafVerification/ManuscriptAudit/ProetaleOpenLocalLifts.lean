import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import PrimalitySheafVerification.ManuscriptAudit.ProetaleOpenRestriction

/-! Vanishing degree-one cohomology of the actual restricted kernel
gives local lifts in the native small pro-étale site. -/

namespace ManuscriptAudit.ProetaleOpenLocalLifts

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open OpenProetaleExtension
open ProetaleOpenRestriction

universe u
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

abbrev identityObject (X : Scheme.{u}) : X.ProEt := Scheme.ProEt.mk (𝟙 X)

/-- The actual open object represented by postcomposition of its identity. -/
abbrev openObject := (proetalePostcompose j).obj (identityObject U)

/-- The actual structure arrow of the open object in the ambient site. -/
def openArrow : openObject j ⟶ identityObject X :=
  MorphismProperty.Over.homMk j (by
    change j ≫ 𝟙 X = 𝟙 U ≫ j
    rw [Category.comp_id, Category.id_comp])

instance openArrow_mono : Mono (openArrow j) where
  right_cancellation f g h := by
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono j).mp
    exact congrArg (fun a ↦ a.left) h

private abbrev R := restriction j G.{u}

/-- Actual local lifting from vanishing native degree-one cohomology. -/
theorem restrictedCokernel_sections_surjective
    {F I : Sheaf (Scheme.ProEt.topology X) G.{u}} (i : F ⟶ I) [Mono i]
    (hVanishing : Subsingleton (Sheaf.H ((R j).obj F) 1)) :
    Function.Surjective ((cokernel.π i).hom.app (op (openObject j))) := by
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
  let W := identityObject U
  let hW : IsTerminal W := MorphismProperty.Over.mkIdTerminal @WeaklyEtale U
  let T := (constantSheaf (Scheme.ProEt.topology U) G.{u}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  change Function.Surjective (QQ.g.hom.app (op W))
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
end ManuscriptAudit.ProetaleOpenLocalLifts

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleOpenLocalLifts.openArrow_mono,
      ``ManuscriptAudit.ProetaleOpenLocalLifts.restrictedCokernel_sections_surjective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
