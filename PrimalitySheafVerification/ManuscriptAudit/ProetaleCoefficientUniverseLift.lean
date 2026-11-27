import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! The actual coefficient universe lift in native pro-étale cohomology
preserves finite limits and chartwise epimorphisms. -/

namespace ManuscriptAudit.ProetaleCoefficientUniverseLift

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{0})

private abbrev A := AddCommGrpCat.{0}
private abbrev B := AddCommGrpCat.{1}
private abbrev J := Scheme.ProEt.topology X
private abbrev U : A ⥤ B := AddCommGrpCat.uliftFunctor.{1}

/-- The very same coefficient functor that appears in native adic cohomology. -/
abbrev lift : Sheaf (J X) A ⥤ Sheaf (J X) B :=
  sheafCompose (J X) U

instance lift_additive : (lift X).Additive where
  map_add {F G} f g := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext W
    change U.map (f.hom.app W + g.hom.app W) = U.map (f.hom.app W) + U.map (g.hom.app W)
    exact U.map_add (f.hom.app W) (g.hom.app W)

instance lift_preservesFiniteLimits : PreservesFiniteLimits (lift X) := by
  let F := sheafToPresheaf (J X) B
  haveI : PreservesFiniteLimits (lift X ⋙ F) := by
    change PreservesFiniteLimits (sheafToPresheaf (J X) A ⋙
      (Functor.whiskeringRight (X.ProEt)ᵒᵖ A B).obj U)
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves (lift X) F

/-- Chartwise epimorphisms are epimorphisms after the actual coefficient universe lift. -/
theorem epi_map_of_chartwise {F G : Sheaf (J X) A} (f : F ⟶ G)
    (h : ∀ W : (X.ProEt)ᵒᵖ, Epi (f.hom.app W)) : Epi ((lift X).map f) := by
  apply (sheafToPresheaf (J X) B).epi_of_epi_map
  apply (NatTrans.epi_iff_epi_app _).mpr
  intro W
  change Epi (U.map (f.hom.app W))
  apply (AddCommGrpCat.epi_iff_surjective _).mpr
  intro y
  obtain ⟨x, hx⟩ := (AddCommGrpCat.epi_iff_surjective _).mp (h W) y.down
  exact ⟨ULift.up x, congrArg ULift.up hx⟩

end
end ManuscriptAudit.ProetaleCoefficientUniverseLift

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleCoefficientUniverseLift.lift_additive,
      ``ManuscriptAudit.ProetaleCoefficientUniverseLift.lift_preservesFiniteLimits,
      ``ManuscriptAudit.ProetaleCoefficientUniverseLift.epi_map_of_chartwise] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
