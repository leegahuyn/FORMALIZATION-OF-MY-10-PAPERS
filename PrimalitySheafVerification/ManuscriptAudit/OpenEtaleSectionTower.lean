import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleCyclicInverseLimit
import PrimalitySheafVerification.ManuscriptAudit.SheafSectionResolutionComplex

/-! Actual compactly supported finite coefficient section complexes and their ℓ-power tower. -/

namespace ManuscriptAudit.OpenEtaleSectionTower

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open OpenComplementRationalPointCohomology (extensionH)
open OpenEtaleCoefficientReduction (extendedConstants sequence reductionH)
open OpenEtaleCyclicInverseLimit (transition)
open SheafSectionResolutionComplex (sectionsTowerFiber)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]

private abbrev A := AddCommGrpCat.{0}
private abbrev M (d : ℕ) := AddCommGrpCat.of (ZMod d)

abbrev coefficients (d : ℕ) := (extendedConstants j).obj (M d)

private def coefficientOrderHom {a b : ℕ} (h : a = b) : coefficients j a ⟶ coefficients j b := by
  subst b
  exact 𝟙 _

private def cohomologyOrderEquiv {a b : ℕ} (h : a = b) (n : ℕ) :
    extensionH j (M a) n ≃+ extensionH j (M b) n := by
  subst b
  exact AddEquiv.refl _

private theorem coefficientOrderHom_Hmap {a b : ℕ} (h : a = b) (n : ℕ)
    (x : extensionH j (M a) n) :
    Sheaf.H.map (coefficientOrderHom j h) n x = cohomologyOrderEquiv j h n x := by
  subst b
  simpa [coefficientOrderHom, cohomologyOrderEquiv] using (Sheaf.H.map_id_apply x)

variable (ℓ : ℕ) [Fact ℓ.Prime]

local instance prime_neZero : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
local instance power_neZero (r : ℕ) : NeZero (ℓ ^ r) :=
  ⟨pow_ne_zero r (Fact.out : ℓ.Prime).ne_zero⟩

/-- The actual map of extended constant sheaves for reduction of the ℓ-power order. -/
def coefficientTransition (r : ℕ) : coefficients j (ℓ ^ (r + 1)) ⟶ coefficients j (ℓ ^ r) :=
  coefficientOrderHom j (pow_succ ℓ r) ≫ (sequence j (ℓ ^ r) ℓ).g

/-- This actual sheaf map induces the previously computed finite cohomology transition. -/
theorem transition_eq_map (n r : ℕ) :
    transition j ℓ n r = Sheaf.H.map (coefficientTransition j ℓ r) n := by
  ext x
  change reductionH j (ℓ ^ r) ℓ n (cohomologyOrderEquiv j (pow_succ ℓ r) n x) =
    Sheaf.H.map (coefficientOrderHom j (pow_succ ℓ r) ≫ (sequence j (ℓ ^ r) ℓ).g) n x
  rw [Sheaf.H.map_comp_apply, coefficientOrderHom_Hmap] <;> rfl

/-- A cochain model of the compactly supported tower, using the actual compactifying
open, the actual coefficient reductions and native injective resolutions. -/
def sectionsFiber : CochainComplex A ℤ := by
  letI := Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology X A
  exact sectionsTowerFiber X.smallEtaleTopology (⊤_ X.Etale)
    (fun r ↦ coefficients j (ℓ ^ r)) (coefficientTransition j ℓ)

end
end ManuscriptAudit.OpenEtaleSectionTower

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.OpenEtaleSectionTower.coefficientTransition,
      ``ManuscriptAudit.OpenEtaleSectionTower.transition_eq_map,
      ``ManuscriptAudit.OpenEtaleSectionTower.sectionsFiber] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
