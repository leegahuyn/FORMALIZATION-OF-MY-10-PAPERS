import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeCompactAdicHTwoAmbient
import PrimalitySheafVerification.ManuscriptAudit.NodalAffineSmoothCompactOpen
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicCompactHTwoEquiv

/-! Compact native degree two of each indicated open is the entire
ambient degree two of its actual proper curve. -/

namespace ManuscriptAudit.NativeCurveCompactAdicHTwo

open AlgebraicGeometry CategoryTheory
open OpenProetaleExtension (extensionByZero)
open ProetaleContinuousDirectImageMaps (functions)
open CuspProperCompactification (projectiveCusp affineOpen projectiveCuspToBase
  projectiveCusp_isProper affineOpen_toBase)
open CuspNativeCompactSmoothHOne (smoothOpen properOrigin_closed)
open CuspProperTwoBoundaryPoints (origin smoothOpen_range smoothOpen_quasiCompact)
open NodalProjectiveClosure (projectiveNode)
open NodalSmoothRationalBoundary (projectiveOrigin projectiveOrigin_closed)
open NodalAffineSmoothCompactOpen (compactOpen compactOpen_range compactOpen_quasiCompact)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K] (ℓ : ℕ) [Fact ℓ.Prime]

private abbrev A := AddCommGrpCat.{1}

private theorem cuspAffine_quasiCompact : QuasiCompact (affineOpen K) := by
  letI : IsProper (projectiveCuspToBase K) := projectiveCusp_isProper K
  letI : QuasiCompact (affineOpen K ≫ projectiveCuspToBase K) := by
    rw [affineOpen_toBase]
    infer_instance
  exact QuasiCompact.of_comp (affineOpen K) (projectiveCuspToBase K)

/-- The literal compact degree-two group of the affine cusp agrees
with the ambient group of its actual proper compactification. -/
def cuspAffineEquiv :
    Sheaf.H ((extensionByZero (affineOpen K) A).obj (functions ℤ_[ℓ] _)) 2 ≃+
      Sheaf.H (functions ℤ_[ℓ] (projectiveCusp K)) 2 := by
  let i := CuspRationalInfinity.infinityPoint K
  letI : IsClosedImmersion i := CuspRationalInfinity.infinityPoint_isClosedImmersion K
  letI : QuasiCompact (affineOpen K) := cuspAffine_quasiCompact K
  exact ProetaleAdicCompactHTwoEquiv.singleEquiv K ℓ (affineOpen K) i (by
    rw [← CuspInfinitySupport.affine_complement_eq_infinity K, compl_compl])

/-- Removing the cusp and infinity gives the same ambient
degree-two group through the actual support map. -/
def cuspSmoothEquiv :
    Sheaf.H ((extensionByZero (smoothOpen K) A).obj (functions ℤ_[ℓ] _)) 2 ≃+
      Sheaf.H (functions ℤ_[ℓ] (projectiveCusp K)) 2 := by
  let i := CuspRationalInfinity.infinityPoint K
  letI : IsClosedImmersion i := CuspRationalInfinity.infinityPoint_isClosedImmersion K
  letI : IsClosedImmersion (origin K) := properOrigin_closed K
  letI : QuasiCompact (smoothOpen K) := smoothOpen_quasiCompact K
  exact ProetaleAdicCompactHTwoEquiv.pairEquiv K ℓ (smoothOpen K) (origin K) i
    (CuspProperTwoBoundaryPoints.boundary_disjoint K) (smoothOpen_range K)

/-- The smooth affine node has the whole proper node group in degree two. -/
def nodalSmoothEquiv :
    Sheaf.H ((extensionByZero (compactOpen K) A).obj (functions ℤ_[ℓ] _)) 2 ≃+
      Sheaf.H (functions ℤ_[ℓ] (projectiveNode K)) 2 := by
  let i := NodalRationalInfinity.infinityPoint K
  letI : IsClosedImmersion i := NodalRationalInfinity.infinityPoint_isClosedImmersion K
  letI : IsClosedImmersion (projectiveOrigin K) := projectiveOrigin_closed K
  letI : QuasiCompact (compactOpen K) := compactOpen_quasiCompact K
  exact ProetaleAdicCompactHTwoEquiv.pairEquiv K ℓ (compactOpen K) (projectiveOrigin K) i
    (NodalAffineSmoothCompactOpen.boundary_disjoint K) (compactOpen_range K)

end
end ManuscriptAudit.NativeCurveCompactAdicHTwo

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NativeCurveCompactAdicHTwo.cuspAffineEquiv,
      ``ManuscriptAudit.NativeCurveCompactAdicHTwo.cuspSmoothEquiv,
      ``ManuscriptAudit.NativeCurveCompactAdicHTwo.nodalSmoothEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
