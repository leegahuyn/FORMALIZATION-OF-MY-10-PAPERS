import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import PrimalitySheafVerification.ManuscriptAudit.ProetaleContinuousDirectImageMaps
import PrimalitySheafVerification.ManuscriptAudit.ProetaleDirectImageHOne
import PrimalitySheafVerification.ManuscriptAudit.ProetaleCohomologyIso

/-! Continuous coefficients give an actual pro-étale H¹ injection
under a universal homeomorphism, directly from chartwise continuity. -/

namespace ManuscriptAudit.ProetaleUniversalHomeomorphismHOne

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleContinuousDirectImageMaps (functions functionsOver diagonal)
open ProetaleCohomologyIso (cohomologyIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {Y X : Scheme.{0}} (p : Y ⟶ X)
  [UniversallyClosed p] [UniversallyInjective p] [Surjective p]
variable (M : Type) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]

private abbrev project (U : X.ProEt) := pullback.fst U.hom p

private theorem project_bijective (U : X.ProEt) : Function.Bijective (project p U) := by
  letI : UniversallyInjective (project p U) := MorphismProperty.pullback_fst U.hom p inferInstance
  letI : Surjective (project p U) := MorphismProperty.pullback_fst U.hom p inferInstance
  exact ⟨(project p U).injective, (project p U).surjective⟩

private theorem component_bijective (U : X.ProEt) :
    Function.Bijective ((diagonal M p).hom.app (op U)) := by
  have h : Function.Bijective (project p U) := project_bijective p U
  constructor
  · intro a b e
    change ULift.{1} (C(U.left, M)) at a b
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    obtain ⟨y, hy⟩ := h.2 x
    have h' := congrArg (fun g : ULift.{1} (C(↥(pullback U.hom p : Scheme.{0}), M)) ↦ g.down y) e
    change a.down (project p U y) = b.down (project p U y) at h'
    rwa [hy] at h'
  · intro s
    let u : C(↥(pullback U.hom p : Scheme.{0}), U.left) := ⟨project p U, (project p U).continuous⟩
    let s' : C(↥(pullback U.hom p : Scheme.{0}), M) := s.down
    have hQuot : Topology.IsQuotientMap u :=
      (project p U).isClosedMap.isQuotientMap (project p U).continuous h.2
    have hFac : Function.FactorsThrough s' u := fun a b e ↦ congrArg s' (h.1 e)
    refine ⟨⟨hQuot.lift s' hFac⟩, ?_⟩
    apply ULift.ext
    exact hQuot.lift_comp s' hFac

/-- Pullback of continuous functions is an isomorphism on the actual native sheaves. -/
theorem diagonal_isIso : IsIso (diagonal M p) := by
  let F := sheafToPresheaf (Scheme.ProEt.topology X) AddCommGrpCat.{1}
  letI : IsIso (F.map (diagonal M p)) := (NatTrans.isIso_iff_isIso_app _).mpr (fun U ↦ by
    let f := (diagonal M p).hom.app U
    let e := AddEquiv.ofBijective f.hom (component_bijective p M U.unop)
    have hIso : IsIso e.toAddCommGrpIso.hom := inferInstance
    exact hIso)
  exact isIso_of_reflects_iso _ F

/-- The degree-one map to the source of the actual universal homeomorphism is injective. -/
def HOneMap : Sheaf.H (functions M X) 1 →+ Sheaf.H (functions M Y) 1 :=
  (ProetaleDirectImageHOne.comparison p (functions M Y)).comp (Sheaf.H.map (diagonal M p) 1)

theorem HOneMap_injective : Function.Injective (HOneMap p M) := by
  letI := diagonal_isIso p M
  exact (ProetaleDirectImageHOne.comparison_injective p (functions M Y)).comp
    (cohomologyIso (X := X) (asIso (diagonal M p)) 1).injective

end
end ManuscriptAudit.ProetaleUniversalHomeomorphismHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleUniversalHomeomorphismHOne.diagonal_isIso,
      ``ManuscriptAudit.ProetaleUniversalHomeomorphismHOne.HOneMap_injective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
