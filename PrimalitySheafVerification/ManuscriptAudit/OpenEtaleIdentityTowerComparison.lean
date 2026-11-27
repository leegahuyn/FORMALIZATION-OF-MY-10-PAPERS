import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleProetaleCompatibleHOne
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleSectionTower

/-! The actual section tower of the identity open uses the ordinary finite
small-étale coefficient tower, with its compatible reductions. -/

namespace ManuscriptAudit.OpenEtaleIdentityTowerComparison

open AlgebraicGeometry CategoryTheory
open EtaleProetaleCompatibleHOne (etaleReduction etaleTransition etaleCompatibleHOne)
open EtaleProetaleFiniteHOneComparison (etaleCoefficient)
open OpenEtaleExtension (extensionByZero extensionByZeroIdIso)
open OpenEtaleCyclicInverseLimit (compatibleClasses transition)
open OpenEtaleSectionTower (transition_eq_map coefficientTransition_eq_map_reduction)
open OpenComplementRationalPointCohomology (extensionH)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (X : Scheme.{0}) (ℓ : ℕ) [Fact ℓ.Prime]

private abbrev A := AddCommGrpCat.{0}

private abbrev level (r : ℕ) := extensionH (𝟙 X) (AddCommGrpCat.of (ZMod (ℓ ^ r))) 1

private abbrev extensionIso (r : ℕ) :=
  (extensionByZeroIdIso X).app (etaleCoefficient X ℓ r)

/-- The coefficient comparison for identity extension, at the actual finite level. -/
def levelEquiv (r : ℕ) : level X ℓ r ≃+ Sheaf.H (etaleCoefficient X ℓ r) 1 :=
  ((Sheaf.functorH X.smallEtaleTopology 1).mapIso
    (extensionIso X ℓ r)).addCommGroupIsoToAddEquiv

theorem levelEquiv_naturality (r : ℕ) (x : level X ℓ (r + 1)) :
    levelEquiv X ℓ r (transition (𝟙 X) ℓ 1 r x) =
      etaleTransition X ℓ r (levelEquiv X ℓ (r + 1) x) := by
  rw [transition_eq_map, coefficientTransition_eq_map_reduction]
  let f := etaleReduction X ℓ r
  let E := extensionByZero (𝟙 X) A
  change Sheaf.H.map (extensionIso X ℓ r).hom 1 (Sheaf.H.map (E.map f) 1 x) =
    Sheaf.H.map f 1 (Sheaf.H.map (extensionIso X ℓ (r + 1)).hom 1 x)
  have h : E.map f ≫ (extensionIso X ℓ r).hom = (extensionIso X ℓ (r + 1)).hom ≫ f :=
    (extensionByZeroIdIso X).hom.naturality f
  calc
    _ = Sheaf.H.map (E.map f ≫ (extensionIso X ℓ r).hom) 1 x :=
      (Sheaf.H.map_comp_apply (E.map f) (extensionIso X ℓ r).hom x).symm
    _ = Sheaf.H.map ((extensionIso X ℓ (r + 1)).hom ≫ f) 1 x :=
      congrArg (fun k ↦ Sheaf.H.map k 1 x) h
    _ = _ := Sheaf.H.map_comp_apply (extensionIso X ℓ (r + 1)).hom f x

set_option maxHeartbeats 1200000 in
/-- Removing the identity extension yields a coherent equivalence of the ordinary degree-one tower. -/
def compatibleEquiv : compatibleClasses (𝟙 X) ℓ 1 ≃+ etaleCompatibleHOne X ℓ :=
  CompatibleTowerCongruence.compatibleEquiv (level X ℓ)
    (fun r ↦ Sheaf.H (etaleCoefficient X ℓ r) 1)
    (transition (𝟙 X) ℓ 1) (etaleTransition X ℓ) (levelEquiv X ℓ) (levelEquiv_naturality X ℓ)

set_option maxHeartbeats 1200000 in
theorem compatibleEquiv_apply (x : compatibleClasses (𝟙 X) ℓ 1) (r : ℕ) :
    (compatibleEquiv X ℓ x).val r = levelEquiv X ℓ r (x.val r) := rfl

end
end ManuscriptAudit.OpenEtaleIdentityTowerComparison

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.OpenEtaleIdentityTowerComparison.levelEquiv_naturality,
      ``ManuscriptAudit.OpenEtaleIdentityTowerComparison.compatibleEquiv,
      ``ManuscriptAudit.OpenEtaleIdentityTowerComparison.compatibleEquiv_apply] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
