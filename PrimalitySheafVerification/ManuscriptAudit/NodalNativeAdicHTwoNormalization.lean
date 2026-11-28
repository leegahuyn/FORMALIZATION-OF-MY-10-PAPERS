import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleExactDirectImageNaturality
import PrimalitySheafVerification.ManuscriptAudit.NodalNativeAdicHTwoNormalizationLinear
import PrimalitySheafVerification.ManuscriptAudit.NativeCurveCompactAdicHTwo

/-! The actual continuous normalizer comparison identifies proper and
compactly supported degree two with the normalization cohomology when
native direct image for the normalization preserves epimorphisms. -/

namespace ManuscriptAudit.NodalNativeAdicHTwoNormalization

open AlgebraicGeometry CategoryTheory
open ProetaleBaseChange (directImage)
open NodalProjectiveClosure (projectiveNode)
open NodalProjectiveNormalization (normalizationMap normalizedNode)
open NodalAffineSmoothCompactOpen (compactOpen)
open OpenProetaleExtension (extensionByZero)
open ProetaleContinuousDirectImageMaps (functions)
open NativeAdicScalarAction (adicModule)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K]
  (l : ℕ) [Fact l.Prime]
  [(directImage (normalizationMap K) AddCommGrpCat.{1}).PreservesEpimorphisms]

local instance : Module ℤ_[l] ((projectiveNode K).EllAdicCohomology l 2) :=
  adicModule (projectiveNode K) l 2
local instance : Module ℤ_[l] ((normalizedNode K).EllAdicCohomology l 2) :=
  adicModule (normalizedNode K) l 2

/-- The original normalization map gives the actual linear comparison. -/
def properEquiv (h₂ : (2 : K) ≠ 0) :
    (projectiveNode K).EllAdicCohomology l 2 ≃ₗ[ℤ_[l]]
      (normalizedNode K).EllAdicCohomology l 2 :=
  (NodalNativeAdicHTwoNormalizationLinear.normalizationImageLinearEquiv K l h₂).trans
    (ProetaleExactDirectImageNaturality.adicLinearEquiv (normalizationMap K) l 2)

/-- The affine nodal smooth locus with compact support gives the same group. -/
def compactEquiv (h₂ : (2 : K) ≠ 0) :
    Sheaf.H ((extensionByZero (compactOpen K) AddCommGrpCat.{1}).obj
      (functions ℤ_[l] _)) 2 ≃+ (normalizedNode K).EllAdicCohomology l 2 :=
  (NativeCurveCompactAdicHTwo.nodalSmoothEquiv K l).trans (properEquiv K l h₂).toAddEquiv

end
end ManuscriptAudit.NodalNativeAdicHTwoNormalization

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalNativeAdicHTwoNormalization.properEquiv,
      ``ManuscriptAudit.NodalNativeAdicHTwoNormalization.compactEquiv] do
    let ax ← collectAxioms name
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
