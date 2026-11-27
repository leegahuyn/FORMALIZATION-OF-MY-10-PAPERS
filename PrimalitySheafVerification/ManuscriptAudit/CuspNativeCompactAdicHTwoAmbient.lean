import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeCompactAffineAdicHTwoLower
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeCompactSmoothAdicHTwoLower
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicCompactHTwoAmbient
import PrimalitySheafVerification.ManuscriptAudit.ProetaleSupportMayerVietoris

/-! Both actual compact degree-two groups of the cusp lie in actual
proper degree two. Their distinguished Laurent generators have the same
proper image, so determining the proper group determines both compact groups. -/

namespace ManuscriptAudit.CuspNativeCompactAdicHTwoAmbient

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CuspProperCompactification (projectiveCusp affineOpen projectiveCuspToBase
  projectiveCusp_isProper affineOpen_toBase)
open CuspProperYChart (lineOpen)
open CuspRationalInfinity (infinityPoint infinityPoint_isClosedImmersion)
open CuspNativeProetaleHTwoLower (overlapOpen fstLeg sndLeg overlap cover)
open CuspNativeAdicHTwoLower (overlapEquiv adicInclusion)
open CuspNativeCompactSmoothHOne (smoothOpen properOrigin_closed)
open CuspProperTwoBoundaryPoints (origin boundary_disjoint smoothOpen_range smoothOpen_quasiCompact)
open ProetaleAdicClosedPairSupport (pairRestriction)
open ProetaleContinuousDirectImageMaps (functions functionsOver diagonal)
open ProetaleCohomologyIso (cohomologyIso)
open ProetaleOpenKernelHOne (restrictionKernelIso restrictionProduct_isZero)
open ProetaleAdicCompactHTwoAmbient
open ProetaleMayerVietorisConnecting (connecting)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K] (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)]

private abbrev A := AddCommGrpCat.{1}
private abbrev X := projectiveCusp K
private abbrev j := affineOpen K
private abbrev k := lineOpen K
private abbrev l := overlapOpen K
private abbrev z := infinityPoint K
private abbrev o := origin K
private abbrev f := functions ℤ_[ℓ] (X K)
private abbrev d₁ := diagonal ℤ_[ℓ] (z K)
private abbrev d₂ := pairRestriction (o K) (z K) ℓ

local instance infinityClosed : IsClosedImmersion (z K) := infinityPoint_isClosedImmersion K
local instance originClosed : IsClosedImmersion (o K) := properOrigin_closed K

private theorem affineOpen_quasiCompact : QuasiCompact (j K) := by
  letI : IsProper (projectiveCuspToBase K) := projectiveCusp_isProper K
  letI : QuasiCompact (j K ≫ projectiveCuspToBase K) := by
    rw [affineOpen_toBase]
    infer_instance
  exact QuasiCompact.of_comp (j K) (projectiveCuspToBase K)

private theorem affine_complement : Set.range (j K) = (Set.range (z K))ᶜ := by
  rw [← CuspInfinitySupport.affine_complement_eq_infinity K, compl_compl]

private theorem overlap_infinity : Disjoint (Set.range (l K)) (Set.range (z K)) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, rfl⟩ hi
  have ha : l K x ∈ Set.range (j K) := ⟨pullback.fst (j K) (k K) x, rfl⟩
  rw [affine_complement K] at ha
  exact ha hi

private def singleZero :
    IsZero ((OpenProetaleExtension.restriction (l K) A).obj (functionsOver ℤ_[ℓ] (z K))) :=
  ProetaleDisjointClosedSupport.restriction_closed_isZero (z K) (l K) ℤ_[ℓ]
    (overlap_infinity K)

private def pairZero :
    IsZero ((OpenProetaleExtension.restriction (l K) A).obj
      (ProetaleAdicClosedPairSupport.boundary (o K) (z K) ℓ)) := by
  let h₀ := ProetaleDisjointClosedSupport.restriction_closed_isZero (o K) (l K) ℤ_[ℓ]
    (CuspNativeCompactSmoothHTwoLower.overlap_disjoint_origin K)
  exact restrictionProduct_isZero (l K) (functionsOver ℤ_[ℓ] (o K))
    (functionsOver ℤ_[ℓ] (z K)) h₀ (singleZero K ℓ)

def affineEquiv :
    CuspNativeCompactAffineAdicHTwoLower.compactHTwo K ℓ ≃+
      (Sheaf.H.map (d₁ K ℓ) 2).ker := by
  letI : QuasiCompact (j K) := affineOpen_quasiCompact K
  exact singleEquiv K ℓ (j K) (z K) (affine_complement K)

def smoothEquiv :
    CuspNativeCompactSmoothAdicHTwoLower.compactHTwo K ℓ ≃+
      (Sheaf.H.map (d₂ K ℓ) 2).ker := by
  letI : QuasiCompact (smoothOpen K) := smoothOpen_quasiCompact K
  exact pairEquiv K ℓ (smoothOpen K) (o K) (z K) (boundary_disjoint K) (smoothOpen_range K)

set_option maxHeartbeats 1600000 in
theorem affineEquiv_inclusion (t : ℤ_[ℓ]) :
    (affineEquiv K ℓ (CuspNativeCompactAffineAdicHTwoLower.inclusion K ℓ t)).val =
      adicInclusion K ℓ t := by
  letI : QuasiCompact (j K) := affineOpen_quasiCompact K
  unfold affineEquiv
  rw [singleEquiv_apply_val]
  let e := cohomologyIso (X := X K)
    (ProetaleAdicClosedSupportKernel.extensionKernelIso (z K) (j K) ℓ (affine_complement K)) 2
  let p := cohomologyIso (X := pullback (j K) (k K))
    (restrictionKernelIso (l K) (d₁ K ℓ) (singleZero K ℓ)) 1
  let w := (overlapEquiv K ℓ).symm t
  change Sheaf.H.map (kernel.ι (d₁ K ℓ)) 2
    (e (e.symm (connecting (j K) (k K) (l K) (fstLeg K) (sndLeg K) (overlap K) (cover K)
      (kernel (d₁ K ℓ)) 1 (p.symm w)))) = adicInclusion K ℓ t
  rw [e.apply_symm_apply]
  exact ProetaleSupportMayerVietoris.connecting_ambient (l K) (d₁ K ℓ) (j K) (k K)
    (fstLeg K) (sndLeg K) (overlap K) (cover K) (singleZero K ℓ) 1 w

set_option maxHeartbeats 1600000 in
theorem smoothEquiv_inclusion (t : ℤ_[ℓ]) :
    (smoothEquiv K ℓ (CuspNativeCompactSmoothAdicHTwoLower.inclusion K ℓ t)).val =
      adicInclusion K ℓ t := by
  letI : QuasiCompact (smoothOpen K) := smoothOpen_quasiCompact K
  unfold smoothEquiv
  rw [pairEquiv_apply_val]
  let e := cohomologyIso (X := X K)
    (ProetaleAdicClosedPairSupport.extensionKernelIso (o K) (z K) ℓ (smoothOpen K)
      (smoothOpen_range K)) 2
  let p := cohomologyIso (X := pullback (j K) (k K))
    (restrictionKernelIso (l K) (d₂ K ℓ) (pairZero K ℓ)) 1
  let w := (overlapEquiv K ℓ).symm t
  change Sheaf.H.map (kernel.ι (d₂ K ℓ)) 2
    (e (e.symm (connecting (j K) (k K) (l K) (fstLeg K) (sndLeg K) (overlap K) (cover K)
      (kernel (d₂ K ℓ)) 1 (p.symm w)))) = adicInclusion K ℓ t
  rw [e.apply_symm_apply]
  exact ProetaleSupportMayerVietoris.connecting_ambient (l K) (d₂ K ℓ) (j K) (k K)
    (fstLeg K) (sndLeg K) (overlap K) (cover K) (pairZero K ℓ) 1 w

theorem compact_inclusions_surjective
    (h : Function.Surjective (adicInclusion K ℓ)) :
    Function.Surjective (CuspNativeCompactAffineAdicHTwoLower.inclusion K ℓ) ∧
      Function.Surjective (CuspNativeCompactSmoothAdicHTwoLower.inclusion K ℓ) := by
  constructor
  · intro a
    obtain ⟨t, ht⟩ := h (affineEquiv K ℓ a).val
    refine ⟨t, (affineEquiv K ℓ).injective (Subtype.ext ?_)⟩
    exact (affineEquiv_inclusion K ℓ t).trans ht
  · intro a
    obtain ⟨t, ht⟩ := h (smoothEquiv K ℓ a).val
    refine ⟨t, (smoothEquiv K ℓ).injective (Subtype.ext ?_)⟩
    exact (smoothEquiv_inclusion K ℓ t).trans ht

end
end ManuscriptAudit.CuspNativeCompactAdicHTwoAmbient

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CuspNativeCompactAdicHTwoAmbient.affineEquiv,
      ``ManuscriptAudit.CuspNativeCompactAdicHTwoAmbient.smoothEquiv,
      ``ManuscriptAudit.CuspNativeCompactAdicHTwoAmbient.affineEquiv_inclusion,
      ``ManuscriptAudit.CuspNativeCompactAdicHTwoAmbient.smoothEquiv_inclusion,
      ``ManuscriptAudit.CuspNativeCompactAdicHTwoAmbient.compact_inclusions_surjective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
