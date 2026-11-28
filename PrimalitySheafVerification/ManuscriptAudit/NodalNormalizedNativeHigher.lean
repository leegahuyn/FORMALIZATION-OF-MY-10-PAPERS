import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineNativeResidueHigher
import PrimalitySheafVerification.ManuscriptAudit.NodalNormalizedNativeHTwoTransition
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicMilnorPositive

/-! Finite native residue cohomology of the genuine normalized projective
node vanishes from degree three. The same holds for its intrinsic adic
cohomology by the actual inverse-limit comparison. -/

namespace ManuscriptAudit.NodalNormalizedNativeHigher

open AlgebraicGeometry CategoryTheory
open ProetaleAdicHOneDetection (finiteCoefficient)
open ProetaleAdicReductionAllDegrees (nativeStep nativeCompatible)
open ProetaleClosedOpenRestriction (restrictionFunctionsIso)
open ProetaleCohomologyIso (cohomologyIso)
open OpenProetaleExtension (restriction)
open NodalProjectiveNormalization (normalizedNode)
open NodalYChartImmersion (nodeYChart)
open NodalYChartOverlap (overlapRing)
open NodalYChartNestedLocalization (denominator overlapCoordinates overlapDenominator)
open NodalNormalizedNativeCharts (yToNormalized zToNormalized)
open NodalNormalizedNativeHTwoBoundary (overlapOpen firstLeg secondLeg overlap cover)
open ProetaleMayerVietorisConnecting (connecting_surjective)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K] (h₂ : (2 : K) ≠ 0)
  (l : ℕ) [Fact l.Prime] [NeZero (l : K)]

private abbrev A := AddCommGrpCat.{1}
private abbrev X := normalizedNode K
private abbrev Y := nodeYChart K
private abbrev Z := Spec (CommRingCat.of (Polynomial K))
private abbrev W := Spec (CommRingCat.of (overlapRing K))

local instance residueTopology (n : ℕ) : TopologicalSpace (ZMod n) := ⊥
local instance residueDiscrete (n : ℕ) : DiscreteTopology (ZMod n) := ⟨rfl⟩

local instance castResidue (r : ℕ) : NeZero ((l ^ r : ℕ) : K) :=
  ⟨by rw [Nat.cast_pow]; exact pow_ne_zero r (NeZero.ne (l : K))⟩

private theorem denominator_nonzero : denominator K ≠ 0 := by
  intro h
  exact (one_ne_zero : (1 : K) ≠ 0)
    (by simpa [denominator] using congrArg (Polynomial.eval (0 : K)) h)

private theorem y_add_two (r n : ℕ) :
    Subsingleton (Sheaf.H (finiteCoefficient (Y K) l r) (n + 2)) := by
  let e := SchemeIsoProetaleCohomology.continuousCohomologyEquiv
    (NodalHigherChartCohomology.chartIso K) (ZMod (l ^ r)) (n + 2)
  have h := AffineNativeResidueHigher.principalOpen_add_two_subsingleton K l r
    (denominator K) (denominator_nonzero K) n
  exact ⟨fun a b ↦ e.injective (h.elim (e a) (e b))⟩

private theorem overlap_add_two (r n : ℕ) :
    Subsingleton (Sheaf.H (finiteCoefficient (W K) l r) (n + 2)) := by
  let j := (Scheme.Spec.mapIso (overlapCoordinates K).toRingEquiv.toCommRingCatIso.op).symm
  let e := SchemeIsoProetaleCohomology.continuousCohomologyEquiv j (ZMod (l ^ r)) (n + 2)
  have hg : overlapDenominator K ≠ 0 := mul_ne_zero (denominator_nonzero K) Polynomial.X_ne_zero
  have h := AffineNativeResidueHigher.principalOpen_add_two_subsingleton K l r _ hg n
  exact ⟨fun a b ↦ e.injective (h.elim (e a) (e b))⟩

private def restrictionEquiv {U : Scheme.{0}} (j : U ⟶ X K) [IsOpenImmersion j]
    (r n : ℕ) :
    Sheaf.H ((restriction j A).obj (finiteCoefficient (X K) l r)) n ≃+
      Sheaf.H (finiteCoefficient U l r) n :=
  cohomologyIso (restrictionFunctionsIso j (ZMod (l ^ r))) n

set_option maxHeartbeats 6200000 in
/-- The genuine finite-coefficient normalization cohomology vanishes in degree n + 3. -/
theorem residue_add_three_subsingleton (r n : ℕ) :
    Subsingleton (Sheaf.H (finiteCoefficient (X K) l r) (n + 3)) := by
  let j := yToNormalized K
  let k := zToNormalized K h₂
  let w := overlapOpen K
  letI := y_add_two K l r (n + 1)
  letI := AffineNativeResidueHigher.affineLine_succ_subsingleton K l r (n + 2)
  let hY : Subsingleton (Sheaf.H ((restriction j A).obj (finiteCoefficient (X K) l r)) (n + 3)) :=
    (restrictionEquiv K l j r (n + 3)).injective.subsingleton
  let hZ : Subsingleton (Sheaf.H ((restriction k A).obj (finiteCoefficient (X K) l r)) (n + 3)) :=
    (restrictionEquiv K l k r (n + 3)).injective.subsingleton
  letI := overlap_add_two K l r n
  letI : Subsingleton (Sheaf.H ((restriction w A).obj (finiteCoefficient (X K) l r)) (n + 2)) :=
    (restrictionEquiv K l w r (n + 2)).injective.subsingleton
  exact (connecting_surjective j k w (firstLeg K) (secondLeg K h₂) (overlap K h₂)
    (cover K h₂) (finiteCoefficient (X K) l r) (n + 2) hY hZ).subsingleton

private theorem step_add_two_surjective (n r : ℕ) :
    Function.Surjective (nativeStep (X K) l (n + 2) r) := by
  cases n with
  | zero => exact NodalNormalizedNativeHTwoTransition.step_surjective K l h₂ r
  | succ m =>
      intro x
      exact ⟨0, (residue_add_three_subsingleton K h₂ l r m).elim _ _⟩

set_option maxHeartbeats 4900000 in
/-- The actual integral adic groups in all degrees at least three vanish as well. -/
theorem adic_add_three_subsingleton (n : ℕ) :
    Subsingleton ((X K).EllAdicCohomology l (n + 3)) := by
  let e := ProetaleAdicMilnorPositive.reductionEquiv (X K) l (n + 1)
    (step_add_two_surjective K h₂ l n)
  have h : Subsingleton (nativeCompatible (X K) l (n + 3)) :=
    ⟨fun x y ↦ Subtype.ext (funext fun r ↦
      (residue_add_three_subsingleton K h₂ l r n).elim _ _)⟩
  exact ⟨fun a b ↦ e.injective (h.elim (e a) (e b))⟩

end
end ManuscriptAudit.NodalNormalizedNativeHigher

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalNormalizedNativeHigher.residue_add_three_subsingleton,
      ``ManuscriptAudit.NodalNormalizedNativeHigher.adic_add_three_subsingleton] do
    let ax ← collectAxioms name
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
