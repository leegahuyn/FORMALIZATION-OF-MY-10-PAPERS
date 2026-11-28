import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeAdicHTwoReductionDetection
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeAdicHTwoRangeCriterion
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicHTwoReductionSurjective

/-! Identification of the actual integral proper-cusp group with its literal
inverse limit, and reduction of integral generation to the finite residue groups. -/

namespace ManuscriptAudit.CuspNativeAdicHTwoInverseLimit

open AlgebraicGeometry
open CuspProperCompactification (projectiveCusp)
open CuspNativeAdicHTwoLower (adicInclusion adicInclusion_injective)
open CuspNativeAdicHTwoReduction (residueInclusion)
open ProetaleAdicReductionAllDegrees (nativeCompatible reductionMap)

noncomputable section

variable (K : Type) [Field K] [IsAlgClosed K] (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)]

/-- The actual native degree-two group is the full coherent finite tower. -/
def reductionEquiv :
    (projectiveCusp K).EllAdicCohomology ℓ 2 ≃+ nativeCompatible (projectiveCusp K) ℓ 2 :=
  AddEquiv.ofBijective (reductionMap (projectiveCusp K) ℓ 2)
    ⟨CuspNativeAdicHTwoReductionDetection.reduction_injective K ℓ,
      ProetaleAdicHTwoReductionSurjective.reduction_surjective (projectiveCusp K) ℓ⟩

/-- If the actual finite groups are cyclic on their Laurent classes, the
actual integral group is the adic integers via the same Laurent class. -/
def adicEquiv_of_finite (h : ∀ n, Function.Surjective (residueInclusion K ℓ n)) :
    ℤ_[ℓ] ≃+ (projectiveCusp K).EllAdicCohomology ℓ 2 :=
  AddEquiv.ofBijective (adicInclusion K ℓ)
    ⟨adicInclusion_injective K ℓ, CuspNativeAdicHTwoRangeCriterion.surjective_of_finite K ℓ
      (CuspNativeAdicHTwoReductionDetection.reduction_injective K ℓ) h⟩

end
end ManuscriptAudit.CuspNativeAdicHTwoInverseLimit

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CuspNativeAdicHTwoInverseLimit.reductionEquiv,
      ``ManuscriptAudit.CuspNativeAdicHTwoInverseLimit.adicEquiv_of_finite] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
