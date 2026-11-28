import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeCompactHigher
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicAmbientInclusion

/-! The compact-to-proper comparison on the actual cusp is the literal
forget-support map in every degree at least two. -/

namespace ManuscriptAudit.CuspNativeCompactAmbientComparison

open AlgebraicGeometry CategoryTheory
open CuspProperCompactification (projectiveCusp affineOpen projectiveCuspToBase
  projectiveCusp_isProper affineOpen_toBase)
open CuspNativeCompactSmoothHOne (smoothOpen properOrigin_closed)
open CuspProperTwoBoundaryPoints (origin smoothOpen_range smoothOpen_quasiCompact)
open CuspRationalInfinity (infinityPoint infinityPoint_isClosedImmersion)
open ProetaleOpenContinuousPullback (ambient)
open ProetaleAdicAmbientInclusion (single_ambient pair_ambient)
open ProetaleContinuousDirectImageMaps (functions)
open CuspNativeCompactHigher (affineEquiv smoothEquiv)
open OpenProetaleExtension (extensionByZero)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K] (ℓ : ℕ) [Fact ℓ.Prime]

private abbrev j := affineOpen K
private abbrev s := smoothOpen K
private abbrev o := origin K
private abbrev z := infinityPoint K
private abbrev A := AddCommGrpCat.{1}

private theorem affine_quasiCompact : QuasiCompact (j K) := by
  letI : IsProper (projectiveCuspToBase K) := projectiveCusp_isProper K
  letI : QuasiCompact (j K ≫ projectiveCuspToBase K) := by
    rw [affineOpen_toBase]
    infer_instance
  exact QuasiCompact.of_comp (j K) (projectiveCuspToBase K)

set_option maxHeartbeats 7300000 in
/-- The affine compact comparison is induced by the actual map into the proper coefficient sheaf. -/
theorem affine_apply (n : ℕ)
    (x : Sheaf.H ((extensionByZero (j K) A).obj (functions ℤ_[ℓ] _)) (n + 2)) :
    affineEquiv K ℓ n x = Sheaf.H.map (ambient ℤ_[ℓ] (j K)) (n + 2) x := by
  letI : QuasiCompact (j K) := affine_quasiCompact K
  letI : IsClosedImmersion (z K) := infinityPoint_isClosedImmersion K
  have h : Set.range (j K) = (Set.range (z K))ᶜ := by
    rw [← CuspInfinitySupport.affine_complement_eq_infinity K, compl_compl]
  let e := ProetaleAdicClosedSupportKernel.extensionKernelIso (z K) (j K) ℓ h
  let a := ProetaleClosedKernelLocalSupport.inc (z K) ℤ_[ℓ]
  change Sheaf.H.map a (n + 2) (Sheaf.H.map e.hom (n + 2) x) = _
  exact (Sheaf.H.map_comp_apply (f := e.hom) (n := n + 2) a x).symm.trans
    (congrArg (fun f ↦ Sheaf.H.map f (n + 2) x) (single_ambient (j K) K ℓ (z K) h))

set_option maxHeartbeats 7600000 in
/-- The smooth compact comparison is induced by the actual map into the proper coefficient sheaf. -/
theorem smooth_apply (n : ℕ)
    (x : Sheaf.H ((extensionByZero (s K) A).obj (functions ℤ_[ℓ] _)) (n + 2)) :
    smoothEquiv K ℓ n x = Sheaf.H.map (ambient ℤ_[ℓ] (s K)) (n + 2) x := by
  letI : QuasiCompact (s K) := smoothOpen_quasiCompact K
  letI : IsClosedImmersion (o K) := properOrigin_closed K
  letI : IsClosedImmersion (z K) := infinityPoint_isClosedImmersion K
  let h := smoothOpen_range K
  let e := ProetaleAdicClosedPairSupport.extensionKernelIso (o K) (z K) ℓ (s K) h
  let a := ProetaleAdicClosedPairSupport.inclusion (o K) (z K) ℓ
  change Sheaf.H.map a (n + 2) (Sheaf.H.map e.hom (n + 2) x) = _
  exact (Sheaf.H.map_comp_apply (f := e.hom) (n := n + 2) a x).symm.trans
    (congrArg (fun f ↦ Sheaf.H.map f (n + 2) x) (pair_ambient (s K) K ℓ (o K) (z K) h))

/-- The literal forget-support map from the affine chart is a bijection in degree at least two. -/
theorem affine_bijective (n : ℕ) :
    Function.Bijective (Sheaf.H.map (ambient ℤ_[ℓ] (j K)) (n + 2)) := by
  have he : ⇑(affineEquiv K ℓ n) = ⇑(Sheaf.H.map (ambient ℤ_[ℓ] (j K)) (n + 2)) :=
    funext (affine_apply K ℓ n)
  rw [← he]
  exact (affineEquiv K ℓ n).bijective

/-- The literal forget-support map from the smooth locus is a bijection in degree at least two. -/
theorem smooth_bijective (n : ℕ) :
    Function.Bijective (Sheaf.H.map (ambient ℤ_[ℓ] (s K)) (n + 2)) := by
  have he : ⇑(smoothEquiv K ℓ n) = ⇑(Sheaf.H.map (ambient ℤ_[ℓ] (s K)) (n + 2)) :=
    funext (smooth_apply K ℓ n)
  rw [← he]
  exact (smoothEquiv K ℓ n).bijective

end
end ManuscriptAudit.CuspNativeCompactAmbientComparison

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``ManuscriptAudit.CuspNativeCompactAmbientComparison.affine_bijective,
      ``ManuscriptAudit.CuspNativeCompactAmbientComparison.smooth_bijective] do
    let ax ← collectAxioms n
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{n} depends on unexpected axioms {ax}"
    logInfo m!"{n} uses {ax}"
