import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import PrimalitySheafVerification.ManuscriptAudit.EssentiallySmallSitePullback
import PrimalitySheafVerification.ManuscriptAudit.EtaleProetaleSiteInclusion

/-! The actual change of sites from the pro-étale site to the small étale
site has a left-exact inverse image on abelian sheaves. -/

namespace ManuscriptAudit.EtaleProetaleInverseImage

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open EtaleProetaleSiteInclusion (inclusion)

universe u

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{u})

private abbrev A := AddCommGrpCat.{u + 1}

/-- Actual restriction from pro-étale to étale sheaves in the cohomology universe. -/
def directImage : Sheaf (Scheme.ProEt.topology X) A.{u} ⥤ Sheaf X.smallEtaleTopology A.{u} :=
  (inclusion X).sheafPushforwardContinuous _ _ _

private theorem exists_inverseImage :
    ∃ L : Sheaf X.smallEtaleTopology A.{u} ⥤ Sheaf (Scheme.ProEt.topology X) A.{u},
      Nonempty (L ⊣ directImage X) ∧ PreservesFiniteLimits L := by
  letI : EssentiallySmall.{u + 1} X.Etale :=
    EssentiallySmall.mk' (AsSmall.equiv : X.Etale ≌ AsSmall.{0} X.Etale)
  letI : EssentiallySmall.{u + 1} X.ProEt := inferInstance
  exact EssentiallySmallSitePullback.exists_leftExactLeftAdjoint
    X.smallEtaleTopology (Scheme.ProEt.topology X) (inclusion X)

/-- The inverse image of the actual continuous site inclusion. -/
def inverseImage : Sheaf X.smallEtaleTopology A.{u} ⥤ Sheaf (Scheme.ProEt.topology X) A.{u} :=
  (exists_inverseImage X).choose

/-- Actual étale-to-pro-étale inverse image and pro-étale-to-étale direct image are adjoint. -/
def adjunction : inverseImage X ⊣ directImage X :=
  (exists_inverseImage X).choose_spec.1.some

instance inverseImage_preservesFiniteLimits : PreservesFiniteLimits (inverseImage X) :=
  (exists_inverseImage X).choose_spec.2

instance inverseImage_isLeftAdjoint : (inverseImage X).IsLeftAdjoint :=
  (adjunction X).isLeftAdjoint

/-- The inverse image identifies the native constant sheaves on the two sites. -/
def constantInverseImageIso :
    constantSheaf X.smallEtaleTopology A.{u} ⋙ inverseImage X ≅
      constantSheaf (Scheme.ProEt.topology X) A.{u} := by
  let T := Scheme.Etale.mk (𝟙 X)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X
  let hU : IsTerminal ((inclusion X).obj T) := IsTerminal.isTerminalObj (inclusion X) T hT
  let a : constantSheaf X.smallEtaleTopology A.{u} ⋙ inverseImage X ⊣
      (sheafSections (Scheme.ProEt.topology X) A.{u}).obj (op ((inclusion X).obj T)) :=
    (constantSheafAdj X.smallEtaleTopology A.{u} hT).comp (adjunction X)
  exact a.leftAdjointUniq (constantSheafAdj (Scheme.ProEt.topology X) A.{u} hU)

end
end ManuscriptAudit.EtaleProetaleInverseImage

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleProetaleInverseImage.adjunction,
      ``ManuscriptAudit.EtaleProetaleInverseImage.inverseImage_preservesFiniteLimits,
      ``ManuscriptAudit.EtaleProetaleInverseImage.constantInverseImageIso] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
