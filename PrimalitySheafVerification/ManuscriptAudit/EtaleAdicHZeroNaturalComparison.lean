import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EllAdicHZeroComparison
import PrimalitySheafVerification.ManuscriptAudit.EtaleDiscreteCoefficientNaturality
import PrimalitySheafVerification.ManuscriptAudit.OpenEtalePrimeTowerArrow
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleSectionTowerComparison
import PrimalitySheafVerification.ManuscriptAudit.ProetalePadicSectionTower

/-! The actual degree-zero comparison uses the same continuous residue sections at every finite level. -/

namespace ManuscriptAudit.EtaleAdicHZeroNaturalComparison

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open EtaleContinuousMapSheaf (continuousMapSheaf constantSheafContinuousMapIso)
open OpenEtaleCoefficientReduction (extendedConstants)
open OpenEtaleExtension (extensionByZero extensionByZeroIdIso)
open OpenEtaleSectionTower (coefficients coefficientTransition transition_eq_map sectionsFiber)
open OpenEtaleCyclicInverseLimit (transition)
open OpenEtalePrimeTowerArrow (residueArrow coefficientTransition_eq_map)
open OpenEtaleTowerDifference (level)
open ProetalePadicSectionTower (compatibleSections sectionTransition continuousSectionsEquiv)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

private abbrev A := AddCommGrpCat.{0}
private abbrev M (d : ℕ) := AddCommGrpCat.of (ZMod d)

local instance residueTopology (d : ℕ) : TopologicalSpace (ZMod d) := ⊥
local instance residueDiscrete (d : ℕ) : DiscreteTopology (ZMod d) := ⟨rfl⟩

variable (X : Scheme.{0})

private abbrev j := 𝟙 X
private abbrev const := constantSheaf X.smallEtaleTopology A

private def finiteSheafIso (d : ℕ) :
    coefficients (j X) d ≅ continuousMapSheaf X (M d) :=
  (extensionByZeroIdIso X).app ((const X).obj (M d)) ≪≫
    constantSheafContinuousMapIso X (M d)

private theorem finiteSheafIso_natural {d e : ℕ} (f : M d ⟶ M e) :
    (extendedConstants (j X)).map f ≫ (finiteSheafIso X e).hom =
      (finiteSheafIso X d).hom ≫ EtaleDiscreteCoefficientNaturality.map X f := by
  let I := extensionByZeroIdIso X
  let C := const X
  let h₁ : (extensionByZero (j X) A).map (C.map f) ≫ (I.app (C.obj (M e))).hom =
      (I.app (C.obj (M d))).hom ≫ C.map f :=
    I.hom.naturality (C.map f)
  let h₂ := EtaleDiscreteCoefficientNaturality.constantIso_natural X f
  change (extensionByZero (j X) A).map (C.map f) ≫
    ((I.app (C.obj (M e))).hom ≫ (constantSheafContinuousMapIso X (M e)).hom) =
    ((I.app (C.obj (M d))).hom ≫ (constantSheafContinuousMapIso X (M d)).hom) ≫
      EtaleDiscreteCoefficientNaturality.map X f
  rw [← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc]

private def terminalObject := Scheme.Etale.mk (𝟙 X)
private def terminalProof : IsTerminal (terminalObject X) :=
  MorphismProperty.Over.mkIdTerminal @Etale X

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- At a finite level, the actual degree-zero sections are the continuous residue sections. -/
def finiteEquiv (r : ℕ) :
    level (j X) ℓ 0 r ≃+ C(X, ZMod (ℓ ^ r)) :=
  ((Sheaf.functorH X.smallEtaleTopology 0).mapIso (finiteSheafIso X (ℓ ^ r))).addCommGroupIsoToAddEquiv.trans
    (Sheaf.H.equiv₀ (continuousMapSheaf X (M (ℓ ^ r))) (terminalProof X))

/-- The genuine finite class transition becomes the genuine pointwise residue reduction. -/
theorem finiteEquiv_natural (r : ℕ) (x : level (j X) ℓ 0 (r + 1)) :
    finiteEquiv X ℓ r (transition (j X) ℓ 0 r x) =
      sectionTransition ℓ X r (finiteEquiv X ℓ (r + 1) x) := by
  let U := continuousMapSheaf X (M (ℓ ^ (r + 1)))
  let V := continuousMapSheaf X (M (ℓ ^ r))
  let u := (finiteSheafIso X (ℓ ^ (r + 1))).hom
  let v := (finiteSheafIso X (ℓ ^ r)).hom
  let q := coefficientTransition (j X) ℓ r
  let t : U ⟶ V := EtaleDiscreteCoefficientNaturality.map X (residueArrow ℓ r)
  have w : q ≫ v = u ≫ t :=
    (congrArg (fun a ↦ a ≫ v) (coefficientTransition_eq_map ℓ (j X) r)).trans
      (finiteSheafIso_natural X (residueArrow ℓ r))
  rw [transition_eq_map]
  change Sheaf.H.equiv₀ V (terminalProof X) (Sheaf.H.map v 0 (Sheaf.H.map q 0 x)) =
    t.hom.app (op (terminalObject X))
      (Sheaf.H.equiv₀ U (terminalProof X) (Sheaf.H.map u 0 x))
  rw [← Sheaf.H.map_comp_apply, w, Sheaf.H.map_comp_apply]
  exact (Sheaf.H.equiv₀_naturality (terminalProof X) t (Sheaf.H.map u 0 x)).symm

/-- The actual ordinary section-tower model and Mathlib's actual pro-étale adic
cohomology agree in degree zero, through identical native finite residue sections. -/
def comparison :
    (sectionsFiber (j X) ℓ).homology 0 ≃+ X.EllAdicCohomology ℓ 0 :=
  (OpenEtaleSectionTowerComparison.zeroEquiv (j X) ℓ).trans
    ((CompatibleTowerCongruence.compatibleEquiv _ _ _ _
      (finiteEquiv X ℓ) (finiteEquiv_natural X ℓ)).trans
      ((continuousSectionsEquiv ℓ X).symm.trans (EllAdicHZeroComparison.continuousEquiv X ℓ).symm))

end
end ManuscriptAudit.EtaleAdicHZeroNaturalComparison

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleAdicHZeroNaturalComparison.finiteEquiv,
      ``ManuscriptAudit.EtaleAdicHZeroNaturalComparison.finiteEquiv_natural,
      ``ManuscriptAudit.EtaleAdicHZeroNaturalComparison.comparison] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
