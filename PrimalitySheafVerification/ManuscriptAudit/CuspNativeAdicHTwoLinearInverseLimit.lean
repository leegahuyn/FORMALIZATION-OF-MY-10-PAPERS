import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeAdicHTwoInverseLimit
import PrimalitySheafVerification.ManuscriptAudit.NativeAdicTowerModule

/-! The actual cohomological inverse-limit identification is linear for the
canonical termwise finite coefficient action on the coherent tower. -/

namespace ManuscriptAudit.CuspNativeAdicHTwoLinearInverseLimit

open AlgebraicGeometry
open CuspProperCompactification (projectiveCusp)

noncomputable section

variable (K : Type) [Field K] [IsAlgClosed K] (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)]

local instance : Module ℤ_[ℓ] ((projectiveCusp K).EllAdicCohomology ℓ 2) :=
  NativeAdicScalarAction.adicModule (projectiveCusp K) ℓ 2

/-- Native proper-cusp H² identifies linearly with the actual finite coefficient tower. -/
def reductionLinearEquiv : (projectiveCusp K).EllAdicCohomology ℓ 2 ≃ₗ[ℤ_[ℓ]]
    NativeAdicTowerModule.tower (projectiveCusp K) ℓ 2 :=
  LinearEquiv.ofBijective (NativeAdicTowerModule.reductionLinear (projectiveCusp K) ℓ 2) (by
    change Function.Bijective (ProetaleAdicReductionAllDegrees.reductionMap (projectiveCusp K) ℓ 2)
    exact (CuspNativeAdicHTwoInverseLimit.reductionEquiv K ℓ).bijective)

end
end ManuscriptAudit.CuspNativeAdicHTwoLinearInverseLimit

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CuspNativeAdicHTwoLinearInverseLimit.reductionLinearEquiv
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
