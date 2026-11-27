import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CompatibleTowerCongruence
import PrimalitySheafVerification.ManuscriptAudit.ComplexTowerCompatibleHomology
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleSectionTower
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleTowerDifference
import PrimalitySheafVerification.ManuscriptAudit.SheafSectionComplexPositiveComparison
import PrimalitySheafVerification.ManuscriptAudit.SheafSectionComplexZeroComparison

/-! Cohomology of the actual compact section tower in terms of its computed finite coefficient classes. -/

namespace ManuscriptAudit.OpenEtaleSectionTowerComparison

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomologicalComplex
open OpenEtaleSectionTower (coefficients coefficientTransition transition_eq_map sectionsFiber)
open OpenEtaleCyclicInverseLimit (transition compatibleClasses)
open OpenEtaleTowerDifference (level)
open SheafSectionResolutionComplex (sectionComplex sectionComplexMap)
open SheafSectionComplexZeroKernel (negativeHomology_subsingleton)
open ComplexTowerCompatibleHomology (fiberHomologyEquiv fiberHomologyEquivOfEpi
  homology_difference_epi_of_epi)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

private abbrev A := AddCommGrpCat.{0}

local instance enoughInjectives (X : Scheme.{0}) : EnoughInjectives (Sheaf X.smallEtaleTopology A) := by
  letI := Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology X A
  infer_instance

variable {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]
variable (ℓ : ℕ) [Fact ℓ.Prime]

private abbrev T (X : Scheme.{0}) := ⊤_ X.Etale
private abbrev J (X : Scheme.{0}) := X.smallEtaleTopology

private abbrev complexes (r : ℕ) :=
  sectionComplex (J X) (T X) (coefficients j (ℓ ^ r))

private abbrev maps (r : ℕ) : complexes j ℓ (r + 1) ⟶ complexes j ℓ r :=
  sectionComplexMap (J X) (T X) (coefficientTransition j ℓ r)

private abbrev datum (n : ℤ) (r : ℕ) := (complexes j ℓ r).homology n

private abbrev diagramMap (n : ℤ) (r : ℕ) : datum j ℓ n (r + 1) ⟶ datum j ℓ n r :=
  homologyMap (maps j ℓ r) n

/-- The finite level of the actual section tower computes the native compact-support cohomology. -/
def levelEquiv (n r : ℕ) : datum j ℓ (n : ℤ) r ≃+ level j ℓ n r :=
  match n with
  | 0 => SheafSectionComplexZeroComparison.cohomologyEquiv (J X)
      (terminalIsTerminal (C := X.Etale)) (coefficients j (ℓ ^ r))
  | n + 1 => SheafSectionComplexPositiveComparison.cohomologyEquiv (J X)
      (terminalIsTerminal (C := X.Etale)) (coefficients j (ℓ ^ r)) n

/-- The finite comparisons intertwine the actual cochain lifts and the native coefficient reductions. -/
theorem levelEquiv_natural (n r : ℕ) (x : datum j ℓ (n : ℤ) (r + 1)) :
    levelEquiv j ℓ n r (diagramMap j ℓ (n : ℤ) r x) =
      transition j ℓ n r (levelEquiv j ℓ n (r + 1) x) := by
  rw [transition_eq_map]
  cases n with
  | zero =>
    exact SheafSectionComplexZeroComparison.cohomologyEquiv_natural (J X)
      (terminalIsTerminal (C := X.Etale)) (coefficientTransition j ℓ r) x
  | succ n =>
    exact SheafSectionComplexPositiveComparison.cohomologyEquiv_natural (J X)
      (terminalIsTerminal (C := X.Etale)) (coefficientTransition j ℓ r) n x

private def compatibleComparison (n : ℕ) :
    CyclicPowerInverseLimit.compatibleTuples (fun r ↦ datum j ℓ (n : ℤ) r)
      (fun r ↦ (diagramMap j ℓ (n : ℤ) r).hom) ≃+ compatibleClasses j ℓ n :=
  CompatibleTowerCongruence.compatibleEquiv _ _ _ _ (levelEquiv j ℓ n) (levelEquiv_natural j ℓ n)

private theorem productHomology_epi (n : ℕ)
    (onto : Function.Surjective (OpenEtaleTowerDifference.difference j ℓ n)) :
    Epi (homologyMap (ComplexTowerDifference.difference (complexes j ℓ) (maps j ℓ)) (n : ℤ)) :=
  homology_difference_epi_of_epi _ _ _
    (AbProductDifference.difference_epi_of_surjective _ _
      (CompatibleTowerCongruence.surjective_of_surjective _ _ _ _
        (levelEquiv j ℓ n) (levelEquiv_natural j ℓ n) onto))

private theorem negative_transition_onto (n : ℤ) (hn : n < 0) (r : ℕ) :
    Function.Surjective (diagramMap j ℓ n r : datum j ℓ n (r + 1) → datum j ℓ n r) := by
  let h := negativeHomology_subsingleton (J X) (T X) (coefficients j (ℓ ^ r)) n hn
  exact fun y ↦ ⟨0, h.elim _ y⟩

/-- Zeroth homology of the actual mapping fiber is the native compatible-class group. -/
def zeroEquiv : (sectionsFiber j ℓ).homology 0 ≃+ compatibleClasses j ℓ 0 := by
  letI := HasDerivedCategory.standard A
  exact (fiberHomologyEquiv (complexes j ℓ) (maps j ℓ) (-1) 0 (by decide)
    (negative_transition_onto j ℓ (-1) (by decide))).trans (compatibleComparison j ℓ 0)

/-- Positive homology of the actual mapping fiber is the native compatible-class group when
the finite cohomology product difference in the preceding degree is onto. -/
def positiveEquiv (n : ℕ)
    (onto : Function.Surjective (OpenEtaleTowerDifference.difference j ℓ n)) :
    (sectionsFiber j ℓ).homology ((n + 1 : ℕ) : ℤ) ≃+ compatibleClasses j ℓ (n + 1) := by
  letI := HasDerivedCategory.standard A
  letI := productHomology_epi j ℓ n onto
  exact (fiberHomologyEquivOfEpi (complexes j ℓ) (maps j ℓ) (n : ℤ) (↑(n + 1) : ℤ)
    (by omega)).trans (compatibleComparison j ℓ (n + 1))

/-- Given surjectivity of all finite product differences, the actual section-tower
mapping fiber computes the native compatible classes in every nonnegative degree. -/
def cohomologyEquiv
    (onto : ∀ n, Function.Surjective (OpenEtaleTowerDifference.difference j ℓ n)) (n : ℕ) :
    (sectionsFiber j ℓ).homology (n : ℤ) ≃+ compatibleClasses j ℓ n :=
  match n with
  | 0 => zeroEquiv j ℓ
  | n + 1 => positiveEquiv j ℓ n (onto n)

/-- The actual compact mapping fiber has zero negative homology. -/
theorem negative_subsingleton (n : ℤ) (hn : n < 0) :
    Subsingleton ((sectionsFiber j ℓ).homology n) := by
  letI := HasDerivedCategory.standard A
  let e := fiberHomologyEquiv (complexes j ℓ) (maps j ℓ) (n - 1) n (by omega)
    (negative_transition_onto j ℓ (n - 1) (by omega))
  refine ⟨fun x y ↦ e.injective (Subtype.ext (funext fun r ↦ ?_))⟩
  exact (negativeHomology_subsingleton (J X) (T X) (coefficients j (ℓ ^ r)) n hn).elim _ _

end
end ManuscriptAudit.OpenEtaleSectionTowerComparison

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.OpenEtaleSectionTowerComparison.levelEquiv,
      ``ManuscriptAudit.OpenEtaleSectionTowerComparison.levelEquiv_natural,
      ``ManuscriptAudit.OpenEtaleSectionTowerComparison.zeroEquiv,
      ``ManuscriptAudit.OpenEtaleSectionTowerComparison.positiveEquiv,
      ``ManuscriptAudit.OpenEtaleSectionTowerComparison.cohomologyEquiv,
      ``ManuscriptAudit.OpenEtaleSectionTowerComparison.negative_subsingleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
