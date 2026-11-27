import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeAdicHTwoResidueRange

/-! Finite-level membership detects the genuine integral Laurent range whenever
the full integral group is separated by its residue tower. -/

namespace ManuscriptAudit.CuspNativeAdicHTwoRangeCriterion

open AlgebraicGeometry CategoryTheory
open CuspProperCompactification (projectiveCusp)
open CuspNativeAdicHTwoLower (adicInclusion)
open CuspNativeAdicHTwoReduction (residueInclusion reduction_adicInclusion)
open ProetaleAdicReductionAllDegrees (nativeCompatible reductionMap)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K] (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)]

private abbrev X := projectiveCusp K

/-- The upper bound for the integral class is implied by the actual finite-level upper bounds. -/
theorem mem_range_iff (h : Function.Injective (reductionMap (X K) ℓ 2))
    (x : (X K).EllAdicCohomology ℓ 2) :
    x ∈ (adicInclusion K ℓ).range ↔
      ∀ n, (reductionMap (X K) ℓ 2 x).val n ∈ (residueInclusion K ℓ n).range := by
  constructor
  · rintro ⟨a, rfl⟩ n
    exact ⟨PadicInt.toZModPow n a, (reduction_adicInclusion K ℓ a n).symm⟩
  · intro hx
    obtain ⟨a, ha, _⟩ := CuspNativeAdicHTwoResidueRange.existsUnique_adicCoordinate K ℓ
      (reductionMap (X K) ℓ 2 x) hx
    refine ⟨a, h (Subtype.ext (funext fun n => ?_))⟩
    exact (reduction_adicInclusion K ℓ a n).trans (ha n)

/-- Actual finite cyclic generation and separatedness imply actual integral cyclic generation. -/
theorem surjective_of_finite (h : Function.Injective (reductionMap (X K) ℓ 2))
    (hs : ∀ n, Function.Surjective (residueInclusion K ℓ n)) :
    Function.Surjective (adicInclusion K ℓ) := by
  intro x
  exact (mem_range_iff K ℓ h x).mpr (fun n => hs n ((reductionMap (X K) ℓ 2 x).val n))

end
end ManuscriptAudit.CuspNativeAdicHTwoRangeCriterion

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CuspNativeAdicHTwoRangeCriterion.mem_range_iff,
      ``ManuscriptAudit.CuspNativeAdicHTwoRangeCriterion.surjective_of_finite] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
