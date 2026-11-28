import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalNativeAdicHTwoNormalization
import PrimalitySheafVerification.ManuscriptAudit.NodalProetaleProperNormalization

/-! The actual continuous normalizer comparison identifies proper and
compactly supported degree two with the cohomology on the actual normalization. -/

namespace ManuscriptAudit.NodalNativeAdicHTwoProper

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

local instance : Module ℤ_[l] ((projectiveNode K).EllAdicCohomology l 2) :=
  adicModule (projectiveNode K) l 2
local instance : Module ℤ_[l] ((normalizedNode K).EllAdicCohomology l 2) :=
  adicModule (normalizedNode K) l 2

private theorem image_preserves (h₂ : (2 : K) ≠ 0) :
    (directImage (normalizationMap K) AddCommGrpCat.{1}).PreservesEpimorphisms where
  preserves α := NodalProetaleProperNormalization.map_epi K h₂ α

/-- The original normalization map gives the actual linear comparison. -/
def properEquiv (h₂ : (2 : K) ≠ 0) :
    (projectiveNode K).EllAdicCohomology l 2 ≃ₗ[ℤ_[l]]
      (normalizedNode K).EllAdicCohomology l 2 := by
  letI := image_preserves K h₂
  exact NodalNativeAdicHTwoNormalization.properEquiv K l h₂

/-- The affine nodal smooth locus with compact support gives the same group. -/
def compactEquiv (h₂ : (2 : K) ≠ 0) :
    Sheaf.H ((extensionByZero (compactOpen K) AddCommGrpCat.{1}).obj
      (functions ℤ_[l] _)) 2 ≃+ (normalizedNode K).EllAdicCohomology l 2 := by
  letI := image_preserves K h₂
  exact NodalNativeAdicHTwoNormalization.compactEquiv K l h₂

end
end ManuscriptAudit.NodalNativeAdicHTwoProper

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalNativeAdicHTwoProper.properEquiv,
      ``ManuscriptAudit.NodalNativeAdicHTwoProper.compactEquiv] do
    let ax ← collectAxioms name
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"

