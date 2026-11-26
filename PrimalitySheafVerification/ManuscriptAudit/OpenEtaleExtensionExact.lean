import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Additive
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleExtensionComposition
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleExtensionMono

/-!
# Exactness of open restriction and extension by zero

Restriction is exact because it has both adjoints. Extension by zero
preserves colimits by its adjunction and preserves monomorphisms by
the checked geometric-stalk comparison, so it also preserves finite
limits.
-/

namespace ManuscriptAudit.OpenEtaleExtension

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev C := AddCommGrpCat.{u}

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

theorem restriction_additive : (restriction j C.{u}).Additive :=
  ⟨by intros; rfl⟩

theorem extensionByZero_additive : (extensionByZero j C.{u}).Additive := by
  letI := restriction_additive j
  exact (abelianExtensionByZeroAdjunction j).left_adjoint_additive

/-- The native restriction functor preserves finite limits and colimits. -/
theorem restriction_exact :
    PreservesFiniteLimits (restriction j C.{u}) ∧
      PreservesFiniteColimits (restriction j C.{u}) := by
  let R := restriction j C.{u}
  letI : R.IsLeftAdjoint := (restrictionDirectImageAdjunction j).isLeftAdjoint
  letI : R.IsRightAdjoint := (abelianExtensionByZeroAdjunction j).isRightAdjoint
  exact ⟨inferInstanceAs (PreservesFiniteLimits R), inferInstanceAs (PreservesFiniteColimits R)⟩

/-- The native extension-by-zero functor preserves finite limits and colimits. -/
theorem extensionByZero_exact :
    PreservesFiniteLimits (extensionByZero j C.{u}) ∧
      PreservesFiniteColimits (extensionByZero j C.{u}) := by
  let F := extensionByZero j C.{u}
  letI : F.IsLeftAdjoint := (abelianExtensionByZeroAdjunction j).isLeftAdjoint
  letI : F.Additive := extensionByZero_additive j
  letI : F.PreservesMonomorphisms :=
    ⟨fun f h => by
      letI : Mono f := h
      exact extensionByZero_map_mono j f⟩
  letI : ∀ {A B : Sheaf U.smallEtaleTopology C.{u}} (f : A ⟶ B),
      PreservesColimit (parallelPair f 0) F := fun _ => inferInstance
  letI : F.PreservesHomology := Functor.preservesHomology_of_preservesMonos_and_cokernels F
  exact ⟨F.preservesFiniteLimits_of_preservesHomology,
    inferInstanceAs (PreservesFiniteColimits F)⟩

end

end ManuscriptAudit.OpenEtaleExtension

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.OpenEtaleExtension.restriction_additive,
      ``ManuscriptAudit.OpenEtaleExtension.extensionByZero_additive,
      ``ManuscriptAudit.OpenEtaleExtension.restriction_exact,
      ``ManuscriptAudit.OpenEtaleExtension.extensionByZero_exact] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
