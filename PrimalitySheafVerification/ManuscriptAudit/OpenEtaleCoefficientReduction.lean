import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.OpenComplementRationalPointCohomology
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleExtensionExact
import PrimalitySheafVerification.ManuscriptAudit.ZModReductionSequence

/-! The canonical coefficient reduction induces the actual long exact sequence for open extension by zero. -/

namespace ManuscriptAudit.OpenEtaleCoefficientReduction

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open OpenEtaleExtension (extensionByZero extensionByZero_additive extensionByZero_exact)
open OpenComplementRationalPointCohomology (extensionH)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

private abbrev A := AddCommGrpCat.{0}

private theorem constant_preservesLimits (U : Scheme.{0}) :
    PreservesFiniteLimits (constantSheaf U.smallEtaleTopology A) := by
  unfold constantSheaf
  infer_instance

variable {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The actual coefficient functor for the displayed open immersion. -/
def extendedConstants : A ⥤ Sheaf X.smallEtaleTopology A :=
  constantSheaf U.smallEtaleTopology A ⋙ extensionByZero j A

instance extendedConstants_additive : (extendedConstants j).Additive := by
  let F := constantSheaf U.smallEtaleTopology A
  letI : PreservesFiniteLimits F := constant_preservesLimits U
  letI : F.Additive := F.additive_of_preserves_binary_products
  letI := extensionByZero_additive j
  unfold extendedConstants
  infer_instance

/-- Open constant extension carries an exact coefficient sequence to a short exact sequence. -/
theorem extendedConstants_shortExact (S : ShortComplex A) (hS : S.ShortExact) :
    (S.map (extendedConstants j)).ShortExact := by
  let F := constantSheaf U.smallEtaleTopology A
  let E := extensionByZero j A
  letI : PreservesFiniteLimits F := constant_preservesLimits U
  letI : F.IsLeftAdjoint :=
    (constantSheafAdj U.smallEtaleTopology A (terminalIsTerminal (C := U.Etale))).isLeftAdjoint
  letI : PreservesFiniteLimits E := (extensionByZero_exact j).1
  letI : PreservesFiniteColimits E := (extensionByZero_exact j).2
  letI : PreservesFiniteLimits (extendedConstants j) := by
    change PreservesFiniteLimits (F ⋙ E)
    infer_instance
  letI : PreservesFiniteColimits (extendedConstants j) := by
    change PreservesFiniteColimits (F ⋙ E)
    infer_instance
  exact hS.map_of_exact (extendedConstants j)

variable (a b : ℕ) [NeZero a] [NeZero b]

/-- The short complex on the ambient scheme induced by the actual coefficient reduction. -/
def sequence : ShortComplex (Sheaf X.smallEtaleTopology A) :=
  (ZModReductionSequence.sequence a b).map (extendedConstants j)

theorem sequence_shortExact : (sequence j a b).ShortExact :=
  extendedConstants_shortExact j _ (ZModReductionSequence.sequence_shortExact a b)

/-- The morphism on cohomology induced by coefficient reduction, with source order a*b. -/
def reductionH (n : ℕ) :
    extensionH j (AddCommGrpCat.of (ZMod (a * b))) n →+
      extensionH j (AddCommGrpCat.of (ZMod a)) n :=
  Sheaf.H.map (sequence j a b).g n

/-- Vanishing of the next kernel-coefficient group implies surjectivity of the actual reduction. -/
theorem reductionH_surjective (n : ℕ)
    (hKer : Subsingleton (extensionH j (AddCommGrpCat.of (ZMod b)) (n + 1))) :
    Function.Surjective (reductionH j a b n) := by
  let S := sequence j a b
  let hS : S.ShortExact := sequence_shortExact j a b
  let Z := (constantSheaf X.smallEtaleTopology A).obj (AddCommGrpCat.of (ULift.{0} ℤ))
  intro x
  have hδ : x.comp hS.extClass (show n + 1 = n + 1 from rfl) = 0 := hKer.elim _ _
  exact Ext.covariant_sequence_exact₃ (X := Z) hS x rfl hδ

end
end ManuscriptAudit.OpenEtaleCoefficientReduction

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.OpenEtaleCoefficientReduction.extendedConstants_shortExact,
      ``ManuscriptAudit.OpenEtaleCoefficientReduction.sequence_shortExact,
      ``ManuscriptAudit.OpenEtaleCoefficientReduction.reductionH,
      ``ManuscriptAudit.OpenEtaleCoefficientReduction.reductionH_surjective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
