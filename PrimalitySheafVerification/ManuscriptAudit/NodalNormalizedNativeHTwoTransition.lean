import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalNormalizedNativeHTwoBoundary
import PrimalitySheafVerification.ManuscriptAudit.NodalNormalizedNativeOverlapCokernel
import PrimalitySheafVerification.ManuscriptAudit.ProetaleKummerResidueHOneTransition
import PrimalitySheafVerification.ManuscriptAudit.ProetaleMayerVietorisNaturality

/-! Actual native degree-two residue transitions on the normalized node
are onto. Use the genuine overlap boundary and lift its class by the
same Kummer unit at the next coefficient level. -/

namespace ManuscriptAudit.NodalNormalizedNativeHTwoTransition

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NodalProjectiveNormalization (normalizedNode normalizationMap)
open NodalNormalizedNativeHTwoBoundary (overlapOpen firstLeg secondLeg overlap cover boundary_surjective)
open NodalNormalizedNativeCharts (yToNormalized zToNormalized)
open NodalNormalizedNativeOverlapCokernel (baseMap)
open NodalYChartOverlap (overlapRing)
open NodalYChartNestedLocalization (overlapCoordinates overlapDenominator)
open ProetaleAdicHOneDetection (finiteCoefficient)
open ProetaleAdicReductionAllDegrees (nativeStep)
open ProetaleMayerVietorisConnecting (connecting)
open ProetaleMayerVietorisNaturality (connecting_naturality)
open ProetaleClosedOpenRestriction (restrictionFunctionsIso)
open ProetaleCohomologyIso (cohomologyIso)
open OpenProetaleExtension (restriction)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K] (l : ℕ)
  [Fact l.Prime] [NeZero (l : K)]

private abbrev A := AddCommGrpCat.{1}
private abbrev X := normalizedNode K
private abbrev W := Spec (CommRingCat.of (overlapRing K))
private abbrev w := overlapOpen K
private abbrev j := yToNormalized K
private abbrev z (h₂ : (2 : K) ≠ 0) := zToNormalized K h₂

local instance residueTopology (n : ℕ) : TopologicalSpace (ZMod n) := ⊥
local instance residueDiscrete (n : ℕ) : DiscreteTopology (ZMod n) := ⟨rfl⟩
local instance castModulus (n : ℕ) : NeZero ((l ^ n : ℕ) : K) :=
  ⟨by rw [Nat.cast_pow]; exact pow_ne_zero n (NeZero.ne (l : K))⟩

private abbrev σ (Y : Scheme.{0}) (n : ℕ) :=
  (ProetaleCoefficientUniverseLift.lift Y).map (ProetaleResidueSheaves.residueTransition Y l n)

private abbrev i (n : ℕ) := restrictionFunctionsIso (w K) (ZMod (l ^ n))

private theorem restriction_natural (n : ℕ) :
    (restriction (w K) A).map (σ l (X K) n) ≫ (i K l n).hom =
      (i K l (n + 1)).hom ≫ σ l (W K) n := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro a
  apply ULift.ext
  exact ContinuousMap.ext (fun _ ↦ rfl)

private theorem overlap_PID : IsPrincipalIdealRing (overlapRing K) := by
  letI : IsPrincipalIdealRing (Localization.Away (overlapDenominator K)) :=
    PrincipalOpenEtaleHTwo.principalIdealRing K (overlapDenominator K)
  exact IsPrincipalIdealRing.of_surjective (overlapCoordinates K).symm
    (overlapCoordinates K).symm.surjective

private theorem restricted_step_surjective (n : ℕ) :
    Function.Surjective (Sheaf.H.map ((restriction (w K) A).map (σ l (X K) n)) 1) := by
  letI := overlap_PID K
  let hi := cohomologyIso (i K l n) 1
  let hj := cohomologyIso (i K l (n + 1)) 1
  have h := ProetaleKummerResidueHOneTransition.step_surjective
    (w K ≫ baseMap K) l (ProetalePIDUnitHOne.HOne_subsingleton (overlapRing K)) n
  intro x
  obtain ⟨y, hy⟩ := h (hi x)
  refine ⟨hj.symm y, hi.injective ?_⟩
  change Sheaf.H.map (i K l n).hom 1
    (Sheaf.H.map ((restriction (w K) A).map (σ l (X K) n)) 1 (hj.symm y)) = hi x
  rw [← Sheaf.H.map_comp_apply, restriction_natural, Sheaf.H.map_comp_apply]
  change nativeStep (W K) l 1 n (hj (hj.symm y)) = hi x
  rw [hj.apply_symm_apply]
  exact hy

set_option maxHeartbeats 5800000 in
/-- The literal residue reductions on the normalized proper group are onto. -/
theorem step_surjective (h₂ : (2 : K) ≠ 0) (n : ℕ) :
    Function.Surjective (nativeStep (X K) l 2 n) := by
  intro x
  obtain ⟨a, ha⟩ := boundary_surjective K h₂ l n x
  obtain ⟨b, hb⟩ := restricted_step_surjective K l n a
  let L := fun r ↦ connecting (j K) (z K h₂) (w K) (firstLeg K) (secondLeg K h₂)
    (overlap K h₂) (cover K h₂) (finiteCoefficient (X K) l r) 1
  refine ⟨L (n + 1) b, ?_⟩
  have h := connecting_naturality (j K) (z K h₂) (w K) (firstLeg K) (secondLeg K h₂)
    (overlap K h₂) (cover K h₂) (σ l (X K) n) 1 b
  exact h.symm.trans ((congrArg (L n) hb).trans ha)

end
end ManuscriptAudit.NodalNormalizedNativeHTwoTransition

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NodalNormalizedNativeHTwoTransition.step_surjective
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{name} depends on unexpected axioms {ax}"
  logInfo m!"{name} uses {ax}"
