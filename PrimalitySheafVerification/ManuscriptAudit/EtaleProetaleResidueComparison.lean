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

/-- Reduction of a small-étale constant coefficient is restriction of the genuine
pro-étale residue reduction under the canonical direct-image identification. -/
theorem residueDirectImageIso_naturality (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) :
    (constantSheaf X.smallEtaleTopology A).map
        (AddCommGrpCat.ofHom (PadicResidueSystems.reduction ℓ (Nat.le_succ n)).toAddMonoidHom) ≫
        (residueDirectImageIso X ℓ n).inv =
      (residueDirectImageIso X ℓ (n + 1)).inv ≫
        (directImage X).map (ProetaleResidueSheaves.residueTransition X ℓ n) := by
  let M := AddCommGrpCat.of (ZMod (ℓ ^ (n + 1)))
  let N := AddCommGrpCat.of (ZMod (ℓ ^ n))
  let f : M ⟶ N :=
    AddCommGrpCat.ofHom (PadicResidueSystems.reduction ℓ (Nat.le_succ n)).toAddMonoidHom
  let g : continuousMapSheaf X M ⟶ continuousMapSheaf X N :=
    (directImage X).map (ProetaleResidueSheaves.residueTransition X ℓ n)
  have h := EtaleContinuousMapSheaf.constantSheafContinuousMapIso_naturality
    X M f g (fun W m ↦ rfl)
  let P := sheafToPresheaf X.smallEtaleTopology A
  apply P.map_injective
  have h' := congrArg (fun q ↦ P.map q) h
  simp only [Functor.map_comp, residueDirectImageIso, discreteDirectImageIso,
    Iso.trans_inv, Iso.symm_inv, Functor.preimageIso_inv, Iso.refl_inv]
  change P.map ((constantSheaf X.smallEtaleTopology A).map f) ≫
      (P.map (constantSheafContinuousMapIso X N).hom ≫ P.map (P.preimage (𝟙 _))) =
    (P.map (constantSheafContinuousMapIso X M).hom ≫ P.map (P.preimage (𝟙 _))) ≫ P.map g
  simp only [P.map_preimage, Category.comp_id]
  simpa only [Functor.map_comp] using h'

end
end ManuscriptAudit.EtaleProetaleResidueComparison

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleProetaleResidueComparison.directImage,
      ``ManuscriptAudit.EtaleProetaleResidueComparison.discreteDirectImageIso,
      ``ManuscriptAudit.EtaleProetaleResidueComparison.residueDirectImageIso,
      ``ManuscriptAudit.EtaleProetaleResidueComparison.residueDirectImageIso_naturality] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
