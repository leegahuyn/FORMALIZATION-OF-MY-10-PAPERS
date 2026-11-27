import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalNativeCompactAdicHOne
import PrimalitySheafVerification.ManuscriptAudit.NodalAffineSmoothCompactOpen
import PrimalitySheafVerification.ManuscriptAudit.NodalNativeAdicHOneLinear
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicPairSupportExact
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicPairSupportScalar
import PrimalitySheafVerification.ManuscriptAudit.AdicLineQuotientSplitting

/-! The actual smooth open of the affine split node has compact native
degree one equal to two copies of the adic integers. -/

namespace ManuscriptAudit.NodalAffineSmoothNativeCompactAdicHOne

open AlgebraicGeometry CategoryTheory
open NodalProjectiveClosure (projectiveNode)
open NodalRationalInfinity (infinityPoint infinityPoint_isClosedImmersion)
open NodalSmoothRationalBoundary (projectiveOrigin projectiveOrigin_closed)
open NodalAffineSmoothCompactOpen (compactOpen compactOpen_range compactOpen_quasiCompact boundary_disjoint)
open NodalNativeCompactAdicHOne (compactHOne)
open ProetaleAdicClosedPairSupport (extensionKernelIso)
open ProetaleAdicPairSupportExact (boundaryClass boundaryClass_injective projection_exact projection_surjective)
open ProetaleAdicPairSupportScalar (supportModule inclusionLinear)
open NativeAdicScalarAction (adicModule)
open ProetaleCohomologyIso (cohomologyIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K] (h₂ : (2 : K) ≠ 0)
variable (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)]

set_option maxHeartbeats 2400000 in
set_option maxRecDepth 2500 in
/-- The actual compact support group of the smooth affine locus has a
boundary-difference line and a split quotient given by the proper conductor class. -/
def compactEquiv : compactHOne (compactOpen K) ℓ ≃+ (ℤ_[ℓ] × ℤ_[ℓ]) := by
  let X := projectiveNode K
  let i₀ := projectiveOrigin K
  let i₁ := infinityPoint K
  let j := compactOpen K
  letI : IsClosedImmersion i₀ := projectiveOrigin_closed K
  letI : IsClosedImmersion i₁ := infinityPoint_isClosedImmersion K
  letI : QuasiCompact j := compactOpen_quasiCompact K
  letI : IrreducibleSpace X := NodalCompactSupportHZero.projectiveNode_irreducible K
  letI := supportModule i₀ i₁ ℓ 1
  letI := adicModule X ℓ 1
  let h := boundary_disjoint K
  let o := cohomologyIso (X := X) (extensionKernelIso i₀ i₁ ℓ j (compactOpen_range K)) 1
  let q := inclusionLinear i₀ i₁ ℓ 1
  let e := NodalNativeAdicHOneLinear.adicHOneLinearEquiv K h₂ ℓ
  let k := boundaryClass K i₀ i₁ ℓ h
  let s := AdicLineQuotientSplitting.splitEquiv k q e (boundaryClass_injective K i₀ i₁ ℓ h)
    (projection_surjective K i₀ i₁ ℓ h) (projection_exact K i₀ i₁ ℓ h)
  exact o.trans (s.symm.trans ((AddEquiv.refl ℤ_[ℓ]).prodCongr e.symm.toAddEquiv))

end
end ManuscriptAudit.NodalAffineSmoothNativeCompactAdicHOne

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NodalAffineSmoothNativeCompactAdicHOne.compactEquiv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
