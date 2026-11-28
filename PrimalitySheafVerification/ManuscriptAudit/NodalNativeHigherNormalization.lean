import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalNativeAdicConductorSequence
import PrimalitySheafVerification.ManuscriptAudit.NodalProetaleRationalImage
import PrimalitySheafVerification.ManuscriptAudit.NodalProetaleProperNormalization
import PrimalitySheafVerification.ManuscriptAudit.ProetaleExactDirectImageCohomology
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAlgebraicallyClosedCohomology
import PrimalitySheafVerification.ManuscriptAudit.ProetaleHigherShortExactEquiv

/-! The genuine conductor sequence compares all degrees at least two on the
proper node and its actual normalization, for both discrete and adic coefficients. -/

namespace ManuscriptAudit.NodalNativeHigherNormalization

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open NodalProjectiveClosure (projectiveNode)
open NodalSmoothRationalBoundary (projectiveOrigin)
open NodalProjectiveNormalization (normalizationMap normalizedNode)
open NodalProetaleConductorSequence (sequence sequence_shortExact)
open ProetaleBaseChange (directImage)
open ProetaleContinuousDirectImageMaps (functions functionsOver)
open ProetaleExactDirectImageCohomology (continuousEquiv)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K]
variable (M : Type) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]

/-- The actual rational singular point's coefficient image has no positive cohomology. -/
theorem rationalImage_H_succ (n : ℕ) :
    Subsingleton (Sheaf.H (functionsOver M (projectiveOrigin K)) (n + 1)) := by
  letI : (directImage (projectiveOrigin K) AddCommGrpCat.{1}).PreservesEpimorphisms where
    preserves a := NodalProetaleRationalImage.map_epi K a
  letI := ProetaleAlgebraicallyClosedCohomology.H_succ_subsingleton K
    (functions M (Spec (CommRingCat.of K))) n
  exact (continuousEquiv (projectiveOrigin K) M (n + 1)).injective.subsingleton

set_option maxHeartbeats 8000000 in
/-- A short exact actual conductor sequence gives the comparison on the
actual normalization in each degree at least two. -/
def normalizationEquiv (h2 : (2 : K) ≠ 0)
    (hS : (sequence K h2 M).ShortExact) (n : ℕ) :
    Sheaf.H (functions M (projectiveNode K)) (n + 2) ≃+
      Sheaf.H (functions M (normalizedNode K)) (n + 2) := by
  let S := sequence K h2 M
  have hSource : Subsingleton (Sheaf.H S.X₃ (n + 1)) :=
    rationalImage_H_succ K M n
  have hTarget : Subsingleton (Sheaf.H S.X₃ (n + 2)) :=
    rationalImage_H_succ K M (n + 1)
  letI : (directImage (normalizationMap K) AddCommGrpCat.{1}).PreservesEpimorphisms where
    preserves a := NodalProetaleProperNormalization.map_epi K h2 a
  exact (ProetaleHigherShortExactEquiv.equivalence S hS (n + 1) hSource hTarget).trans
    (continuousEquiv (normalizationMap K) M (n + 2))

/-- Actual proper normalization comparison for any discrete abelian coefficient. -/
def discreteEquiv [DiscreteTopology M] (h2 : (2 : K) ≠ 0) (n : ℕ) :
    Sheaf.H (functions M (projectiveNode K)) (n + 2) ≃+
      Sheaf.H (functions M (normalizedNode K)) (n + 2) :=
  normalizationEquiv K M h2 (sequence_shortExact K h2 M) n

/-- Actual proper normalization comparison for integral adic coefficients. -/
def adicEquiv (l : ℕ) [Fact l.Prime] (h2 : (2 : K) ≠ 0) (n : ℕ) :
    (projectiveNode K).EllAdicCohomology l (n + 2) ≃+
      (normalizedNode K).EllAdicCohomology l (n + 2) :=
  normalizationEquiv K ℤ_[l] h2 (NodalNativeAdicConductorSequence.shortExact K h2 l) n

end
end ManuscriptAudit.NodalNativeHigherNormalization

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalNativeHigherNormalization.rationalImage_H_succ,
      ``ManuscriptAudit.NodalNativeHigherNormalization.discreteEquiv,
      ``ManuscriptAudit.NodalNativeHigherNormalization.adicEquiv] do
    let ax ← collectAxioms name
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
