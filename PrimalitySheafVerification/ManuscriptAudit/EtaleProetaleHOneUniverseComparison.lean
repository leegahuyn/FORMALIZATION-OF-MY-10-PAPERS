import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleCoefficientHOne
import PrimalitySheafVerification.ManuscriptAudit.EtaleProetaleHOne
import PrimalitySheafVerification.ManuscriptAudit.EtaleProetaleResidueComparison
import PrimalitySheafVerification.ManuscriptAudit.ProetaleCoefficientUniverseLift

/-! The native pro-étale H¹ comparison detects small-universe étale
classes of the actual direct image of the original coefficient sheaf. -/

namespace ManuscriptAudit.EtaleProetaleHOneUniverseComparison

open AlgebraicGeometry CategoryTheory Opposite

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt
attribute [local instance] EtaleCoefficientHOne.highExt

variable (X : Scheme.{0})

private abbrev A := AddCommGrpCat.{0}
private abbrev B := AddCommGrpCat.{1}
private abbrev D := Sheaf (Scheme.ProEt.topology X) A

private abbrev etaleLift := EtaleCoefficientUniverseLift.lift X
private abbrev proetaleLift := ProetaleCoefficientUniverseLift.lift X
private abbrev direct₀ := EtaleProetaleResidueComparison.directImage X
private abbrev direct₁ := EtaleProetaleInverseImage.directImage X

/-- Actual restriction and coefficient universe lift commute on the underlying diagrams. -/
def directImageLiftIso (F : D X) :
    (etaleLift X).obj ((direct₀ X).obj F) ≅ (direct₁ X).obj ((proetaleLift X).obj F) := by
  let G := sheafToPresheaf X.smallEtaleTopology B
  exact G.preimageIso
    (Functor.associator (EtaleProetaleSiteInclusion.inclusion X).op F.obj
      (AddCommGrpCat.uliftFunctor.{1} : A ⥤ B))

/-- The native degree-one map from small-universe étale direct image cohomology. -/
def comparison (F : D X) :
    Sheaf.H ((direct₀ X).obj F) 1 →+ Sheaf.H ((proetaleLift X).obj F) 1 :=
  ((EtaleProetaleHOne.comparison X ((proetaleLift X).obj F)).comp
    (Sheaf.H.map (directImageLiftIso X F).hom 1)).comp
    (EtaleCoefficientHOne.comparison X ((direct₀ X).obj F))

/-- The actual degree-one comparison is injective. -/
theorem comparison_injective (F : D X) : Function.Injective (comparison X F) := by
  let e := directImageLiftIso X F
  have h : Function.LeftInverse (Sheaf.H.map e.inv 1) (Sheaf.H.map e.hom 1) := by
    intro z
    rw [← Sheaf.H.map_comp_apply, e.hom_inv_id, Sheaf.H.map_id_apply]
  intro x y hxy
  apply EtaleCoefficientHOne.comparison_injective X ((direct₀ X).obj F)
  apply h.injective
  apply EtaleProetaleHOne.comparison_injective X ((proetaleLift X).obj F)
  exact hxy

end
end ManuscriptAudit.EtaleProetaleHOneUniverseComparison

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleProetaleHOneUniverseComparison.directImageLiftIso,
      ``ManuscriptAudit.EtaleProetaleHOneUniverseComparison.comparison_injective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
