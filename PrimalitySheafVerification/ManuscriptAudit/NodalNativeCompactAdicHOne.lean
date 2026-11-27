import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicOpenClosedHOne
import PrimalitySheafVerification.ManuscriptAudit.NodalNativeAdicHOne
import PrimalitySheafVerification.ManuscriptAudit.NodalRationalInfinity
import PrimalitySheafVerification.ManuscriptAudit.NodalSmoothRationalBoundary

/-! Actual native compact adic H¹ of the affine node and the smooth
locus of its proper model, with the indicated rational boundary points. -/

namespace ManuscriptAudit.NodalNativeCompactAdicHOne

open AlgebraicGeometry CategoryTheory
open NodalProjectiveClosure (projectiveNode affineOpen affineOpen_toBase
  projectiveNodeToBase projectiveNode_isProper)
open NodalRationalInfinity (infinityPoint infinityPoint_isClosedImmersion affine_complement_eq_infinity)
open NodalSmoothRationalBoundary (projectiveOrigin projectiveOrigin_closed smooth_range)
open NodalSmoothLocusOverlap (smoothOpen)
open ProetaleContinuousDirectImageMaps (functions)
open OpenProetaleExtension (extensionByZero)
open ProetaleAdicOpenClosedHOne (compactHOneEquiv)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

abbrev compactHOne {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]
    (ℓ : ℕ) [Fact ℓ.Prime] :=
  Sheaf.H ((extensionByZero j AddCommGrpCat.{1}).obj (functions ℤ_[ℓ] U)) 1

variable (K : Type) [Field K] [IsAlgClosed K] (ℓ : ℕ) [Fact ℓ.Prime]

private theorem affineOpen_quasiCompact : QuasiCompact (affineOpen K) := by
  letI : IsProper (projectiveNodeToBase K) := projectiveNode_isProper K
  letI : QuasiCompact (affineOpen K ≫ projectiveNodeToBase K) := by
    rw [affineOpen_toBase]
    infer_instance
  exact QuasiCompact.of_comp (affineOpen K) (projectiveNodeToBase K)

/-- Compact H¹ of the actual affine node maps bijectively to H¹ of its proper closure. -/
def affineToProper : compactHOne (affineOpen K) ℓ ≃+ (projectiveNode K).EllAdicCohomology ℓ 1 := by
  let i := infinityPoint K
  let j := affineOpen K
  letI : IsClosedImmersion i := infinityPoint_isClosedImmersion K
  letI : QuasiCompact j := affineOpen_quasiCompact K
  have h : Set.range j = (Set.range i)ᶜ := by
    change Set.range (affineOpen K) = (Set.range (infinityPoint K))ᶜ
    rw [← affine_complement_eq_infinity K, compl_compl]
  exact compactHOneEquiv K i ℓ j h

/-- Compact H¹ of the actual proper smooth open maps bijectively to ambient H¹. -/
def smoothToProper : compactHOne (smoothOpen K).ι ℓ ≃+ (projectiveNode K).EllAdicCohomology ℓ 1 := by
  let i := projectiveOrigin K
  let j := (smoothOpen K).ι
  letI : IsClosedImmersion i := projectiveOrigin_closed K
  letI : QuasiCompact j := NodalProjectiveNormalization.smoothInclusion_quasiCompact K
  exact compactHOneEquiv K i ℓ j (smooth_range K)

variable [NeZero (ℓ : K)]

/-- The actual affine nodal compact H¹ is one copy of the adic integers. -/
def affineEquiv (h₂ : (2 : K) ≠ 0) : compactHOne (affineOpen K) ℓ ≃+ ℤ_[ℓ] :=
  (affineToProper K ℓ).trans (NodalNativeAdicHOne.adicHOneEquiv K h₂ ℓ)

/-- The actual smooth locus of the proper split node has compact H¹ of rank one. -/
def smoothEquiv (h₂ : (2 : K) ≠ 0) : compactHOne (smoothOpen K).ι ℓ ≃+ ℤ_[ℓ] :=
  (smoothToProper K ℓ).trans (NodalNativeAdicHOne.adicHOneEquiv K h₂ ℓ)

end
end ManuscriptAudit.NodalNativeCompactAdicHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalNativeCompactAdicHOne.affineToProper,
      ``ManuscriptAudit.NodalNativeCompactAdicHOne.smoothToProper,
      ``ManuscriptAudit.NodalNativeCompactAdicHOne.affineEquiv,
      ``ManuscriptAudit.NodalNativeCompactAdicHOne.smoothEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
