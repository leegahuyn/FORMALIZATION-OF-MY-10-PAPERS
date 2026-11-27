import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import PrimalitySheafVerification.ManuscriptAudit.EssentiallySmallSitePullback
import PrimalitySheafVerification.ManuscriptAudit.ProetaleBaseChange

/-! The actual change of small pro-étale sites of any scheme morphism
has a left-exact inverse image preserving constant sheaves. -/

namespace ManuscriptAudit.ProetaleInverseImage

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleBaseChange (baseChange directImage)

universe u
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

private abbrev A := AddCommGrpCat.{u + 1}
private abbrev C (Z : Scheme.{u}) := Sheaf (Scheme.ProEt.topology Z) A.{u}

private theorem exists_inverseImage :
    ∃ L : C Y ⥤ C X, Nonempty (L ⊣ directImage f A.{u}) ∧ PreservesFiniteLimits L := by
  letI : EssentiallySmall.{u + 1} Y.ProEt := inferInstance
  letI : EssentiallySmall.{u + 1} X.ProEt := inferInstance
  exact EssentiallySmallSitePullback.exists_leftExactLeftAdjoint
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) (baseChange f)

/-- The left-exact inverse image of the actual morphism of native pro-étale sites. -/
def inverseImage : C Y ⥤ C X :=
  (exists_inverseImage f).choose

def adjunction : inverseImage f ⊣ directImage f A.{u} :=
  (exists_inverseImage f).choose_spec.1.some

instance inverseImage_preservesFiniteLimits : PreservesFiniteLimits (inverseImage f) :=
  (exists_inverseImage f).choose_spec.2

instance inverseImage_isLeftAdjoint : (inverseImage f).IsLeftAdjoint :=
  (adjunction f).isLeftAdjoint

instance inverseImage_additive : (inverseImage f).Additive :=
  Functor.additive_of_preserves_binary_products (inverseImage f)

/-- The actual inverse image commutes with the constant-sheaf functor. -/
def constantInverseImageIso :
    constantSheaf (Scheme.ProEt.topology Y) A.{u} ⋙ inverseImage f ≅
      constantSheaf (Scheme.ProEt.topology X) A.{u} := by
  let T := Scheme.ProEt.mk (𝟙 Y)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal @WeaklyEtale Y
  let hU : IsTerminal ((baseChange f).obj T) := IsTerminal.isTerminalObj (baseChange f) T hT
  let a : constantSheaf (Scheme.ProEt.topology Y) A.{u} ⋙ inverseImage f ⊣
      (sheafSections (Scheme.ProEt.topology X) A.{u}).obj (op ((baseChange f).obj T)) :=
    (constantSheafAdj (Scheme.ProEt.topology Y) A.{u} hT).comp (adjunction f)
  exact a.leftAdjointUniq (constantSheafAdj (Scheme.ProEt.topology X) A.{u} hU)

end
end ManuscriptAudit.ProetaleInverseImage

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleInverseImage.adjunction,
      ``ManuscriptAudit.ProetaleInverseImage.inverseImage_preservesFiniteLimits,
      ``ManuscriptAudit.ProetaleInverseImage.constantInverseImageIso] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
