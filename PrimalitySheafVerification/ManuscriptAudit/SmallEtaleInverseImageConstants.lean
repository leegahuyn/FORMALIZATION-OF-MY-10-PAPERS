import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleBaseChange

/-! Every actual inverse-image adjoint of small étale direct image takes
constant sheaves to constant sheaves. -/

namespace ManuscriptAudit.SmallEtaleInverseImageConstants

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v w

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable (A : Type v) [Category.{w} A]
variable [HasWeakSheafify X.smallEtaleTopology A] [HasWeakSheafify Y.smallEtaleTopology A]
variable {L : Sheaf Y.smallEtaleTopology A ⥤ Sheaf X.smallEtaleTopology A}

/-- Constant sheaves commute with any left adjoint to actual small étale
direct image. Pullback of the identity étale object is terminal. -/
def inverseImageConstantIso (adj : L ⊣ SmallEtaleBaseChange.directImage f A) :
    constantSheaf Y.smallEtaleTopology A ⋙ L ≅ constantSheaf X.smallEtaleTopology A := by
  let T := Scheme.Etale.mk (𝟙 Y)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale Y
  let G := SmallEtaleBaseChange.etaleBaseChange f
  letI : PreservesFiniteLimits G := SmallEtaleBaseChange.preservesFiniteLimits f
  let hG : IsTerminal (G.obj T) := IsTerminal.isTerminalObj G T hT
  let c : constantSheaf Y.smallEtaleTopology A ⋙ L ⊣
      (sheafSections X.smallEtaleTopology A).obj (op (G.obj T)) :=
    (constantSheafAdj Y.smallEtaleTopology A hT).comp adj
  exact c.leftAdjointUniq (constantSheafAdj X.smallEtaleTopology A hG)

/-- The coefficient object is unchanged under the actual inverse image
of its constant sheaf. -/
def inverseImageConstantObjectIso (adj : L ⊣ SmallEtaleBaseChange.directImage f A) (M : A) :
    L.obj ((constantSheaf Y.smallEtaleTopology A).obj M) ≅
      (constantSheaf X.smallEtaleTopology A).obj M :=
  (inverseImageConstantIso f A adj).app M

end
end ManuscriptAudit.SmallEtaleInverseImageConstants

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.SmallEtaleInverseImageConstants.inverseImageConstantIso
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
