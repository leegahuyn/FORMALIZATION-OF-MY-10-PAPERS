import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.OpenProetaleExtension
import PrimalitySheafVerification.ManuscriptAudit.DownwardClosedLanFiniteLimits

/-! Native pro-étale extension by zero is exact for an open immersion
because its pointwise presheaf Kan extension is already left exact. -/

namespace ManuscriptAudit.ProetaleOpenExtensionExact

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open OpenProetaleExtension

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]

private abbrev A := AddCommGrpCat.{1}
private abbrev P := proetalePostcompose j

private theorem downward_closed (W : X.ProEtᵒᵖ) (a : CostructuredArrow (P j).op W) :
    ∃ V : U.ProEtᵒᵖ, Nonempty ((P j).op.obj V ≅ W) := by
  let Y := a.left.unop
  let g : W.unop ⟶ (P j).obj Y := a.hom.unop
  have h : (g.left ≫ Y.hom) ≫ j = W.unop.hom := by
    simpa only [Category.assoc, MorphismProperty.Over.map_obj_hom] using
      MorphismProperty.Over.w g
  letI : WeaklyEtale ((g.left ≫ Y.hom) ≫ j) := by
    rw [h]
    exact W.unop.prop
  let V : U.ProEt := MorphismProperty.Over.mk ⊤ (g.left ≫ Y.hom) (WeaklyEtale.of_comp _ j)
  let e : (P j).obj V ≅ W.unop := MorphismProperty.Over.isoMk (Iso.refl W.unop.left) (by
    change 𝟙 W.unop.left ≫ W.unop.hom = (g.left ≫ Y.hom) ≫ j
    simpa only [Category.id_comp] using h.symm)
  exact ⟨op V, ⟨e.op.symm⟩⟩

set_option maxHeartbeats 1400000 in
/-- The actual pro-étale extension-by-zero functor preserves finite limits. -/
theorem extensionByZero_preservesFiniteLimits :
    PreservesFiniteLimits (extensionByZero j A) := by
  letI : (P j).Full := (postcomposeFullyFaithful j).full
  letI : (P j).Faithful := (postcomposeFullyFaithful j).faithful
  letI : ∀ F : U.ProEtᵒᵖ ⥤ A, (P j).op.HasLeftKanExtension F := hasLeftKanExtension j A
  letI : PreservesFiniteLimits ((P j).op.lan : (U.ProEtᵒᵖ ⥤ A) ⥤ X.ProEtᵒᵖ ⥤ A) :=
    DownwardClosedLanFiniteLimits.lan_preservesFiniteLimits (P j).op
      (hasPointwiseLeftKanExtension j A) (downward_closed j)
  change PreservesFiniteLimits (sheafToPresheaf (Scheme.ProEt.topology U) A ⋙
    (P j).op.lan ⋙ presheafToSheaf (Scheme.ProEt.topology X) A)
  infer_instance

/-- Extension by zero also preserves finite colimits by the actual adjunction. -/
theorem extensionByZero_preservesFiniteColimits :
    PreservesFiniteColimits (extensionByZero j A) := by
  letI : (extensionByZero j A).IsLeftAdjoint := (abelianExtensionByZeroAdjunction j).isLeftAdjoint
  infer_instance

/-- Restriction to an actual pro-étale open takes injective sheaves to injective sheaves. -/
theorem restriction_injective (F : Sheaf (Scheme.ProEt.topology X) A) (hF : Injective F) :
    Injective ((restriction j A).obj F) := by
  letI := extensionByZero_preservesFiniteLimits j
  exact (abelianExtensionByZeroAdjunction j).map_injective F hF

end
end ManuscriptAudit.ProetaleOpenExtensionExact

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleOpenExtensionExact.extensionByZero_preservesFiniteLimits,
      ``ManuscriptAudit.ProetaleOpenExtensionExact.extensionByZero_preservesFiniteColimits,
      ``ManuscriptAudit.ProetaleOpenExtensionExact.restriction_injective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
