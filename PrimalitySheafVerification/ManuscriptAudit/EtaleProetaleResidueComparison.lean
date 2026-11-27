import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleContinuousMapSheaf
import PrimalitySheafVerification.ManuscriptAudit.EtaleProetaleSiteInclusion
import PrimalitySheafVerification.ManuscriptAudit.ProetaleResidueSheaves

/-! Degree-zero small-étale direct image of the actual discrete pro-étale residue sheaves. -/

namespace ManuscriptAudit.EtaleProetaleResidueComparison

open AlgebraicGeometry CategoryTheory
open EtaleProetaleSiteInclusion (inclusion)
open ProetaleResidueSheaves (continuousCoefficients residueSheaf)
open EtaleContinuousMapSheaf (continuousMapSheaf constantSheafContinuousMapIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{0}

variable (X : Scheme.{0})

/-- The actual small-étale direct image of a pro-étale sheaf along the site inclusion. -/
def directImage : Sheaf (Scheme.ProEt.topology X) A ⥤ Sheaf X.smallEtaleTopology A :=
  (inclusion X).sheafPushforwardContinuous A X.smallEtaleTopology (Scheme.ProEt.topology X)

/-- Restricting continuous discrete-valued sections gives the actual small-étale constant sheaf. -/
def discreteDirectImageIso (M : AddCommGrpCat.{0}) [TopologicalSpace M] [DiscreteTopology M]
    [IsTopologicalAddGroup M] :
    (directImage X).obj (continuousCoefficients X M) ≅ (constantSheaf X.smallEtaleTopology A).obj M := by
  let G := sheafToPresheaf X.smallEtaleTopology A
  have e : G.obj ((directImage X).obj (continuousCoefficients X M)) ≅
      G.obj (continuousMapSheaf X M) := Iso.refl _
  exact G.preimageIso e ≪≫ (constantSheafContinuousMapIso X M).symm

local instance residueTopology (d : ℕ) : TopologicalSpace (ZMod d) := ⊥
local instance residueDiscrete (d : ℕ) : DiscreteTopology (ZMod d) := ⟨rfl⟩

/-- The actual native finite residue sheaves push forward to the corresponding small-étale constants. -/
def residueDirectImageIso (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) :
    (directImage X).obj (residueSheaf X ℓ n) ≅
      (constantSheaf X.smallEtaleTopology A).obj (AddCommGrpCat.of (ZMod (ℓ ^ n))) :=
  discreteDirectImageIso X (AddCommGrpCat.of (ZMod (ℓ ^ n)))

end
end ManuscriptAudit.EtaleProetaleResidueComparison

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleProetaleResidueComparison.directImage,
      ``ManuscriptAudit.EtaleProetaleResidueComparison.discreteDirectImageIso,
      ``ManuscriptAudit.EtaleProetaleResidueComparison.residueDirectImageIso] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
