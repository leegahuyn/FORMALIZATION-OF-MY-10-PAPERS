import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalNativeAdicHTwoNormalizerImage
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicDirectImageScalar

/-! The actual integral degree-two comparison of the proper nodal curve
with its normalization coefficient image respects the intrinsic adic action. -/

namespace ManuscriptAudit.NodalNativeAdicHTwoNormalizationLinear

open AlgebraicGeometry CategoryTheory
open NodalProjectiveClosure (projectiveNode)
open NodalProjectiveNormalization (normalizationMap)
open ProetaleContinuousDirectImageMaps (functionsOver diagonal)
open ProetaleAdicDirectImageScalar (imageModule diagonal_map_smul)
open NodalNativeAdicHTwoNormalizerImage (normalizationImageEquiv)
open NativeAdicScalarAction (adicModule)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K]
variable (ℓ : ℕ) [Fact ℓ.Prime]

local instance : Module ℤ_[ℓ] ((projectiveNode K).EllAdicCohomology ℓ 2) :=
  adicModule (projectiveNode K) ℓ 2
local instance : Module ℤ_[ℓ] (Sheaf.H (functionsOver ℤ_[ℓ] (normalizationMap K)) 2) :=
  imageModule (normalizationMap K) ℓ 2

/-- This is the genuine normalization diagonal on native cohomology,
with the original continuous coefficient actions on both sides. -/
def normalizationImageLinearEquiv (h2 : (2 : K) ≠ 0) :
    (projectiveNode K).EllAdicCohomology ℓ 2 ≃ₗ[ℤ_[ℓ]]
      Sheaf.H (functionsOver ℤ_[ℓ] (normalizationMap K)) 2 where
  __ := normalizationImageEquiv K ℓ h2
  map_smul' a x := by
    change Sheaf.H.map (diagonal ℤ_[ℓ] (normalizationMap K)) 2 (a • x) =
      a • Sheaf.H.map (diagonal ℤ_[ℓ] (normalizationMap K)) 2 x
    exact diagonal_map_smul (normalizationMap K) ℓ 2 a x

end
end ManuscriptAudit.NodalNativeAdicHTwoNormalizationLinear

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NodalNativeAdicHTwoNormalizationLinear.normalizationImageLinearEquiv
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{name} depends on unexpected axioms {ax}"
  logInfo m!"{name} uses {ax}"
