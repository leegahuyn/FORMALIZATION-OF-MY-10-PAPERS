import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeProperAdicPower
import PrimalitySheafVerification.ManuscriptAudit.CuspRelativePowerSmoothOpen
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicAmbientInclusion
import PrimalitySheafVerification.ManuscriptAudit.CuspProperTwoBoundaryPoints

/-! Actual compactly supported integral ℓ-adic pullback on the original
affine and regular opens of the cusp is scalar under relative power. -/

namespace ManuscriptAudit.CuspNativeCompactAdicRelativePower

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CuspProperCompactification (projectiveCusp affineOpen projectiveCuspToBase
  projectiveCusp_isProper affineOpen_toBase)
open CuspRelativePowerMap (projectiveMap affineMap)
open CuspRelativePowerCartesian (affine_isPullback)
open CuspRelativePowerSmoothOpen (smoothMap smooth_isPullback)
open CuspNativeCompactSmoothHOne (smoothOpen properOrigin_closed)
open CuspProperTwoBoundaryPoints (origin smoothOpen_range smoothOpen_quasiCompact boundary_disjoint)
open CuspRationalInfinity (infinityPoint infinityPoint_isClosedImmersion)
open ProetaleOpenContinuousPullback (ambient compactMap ambient_naturality)
open ProetaleAdicAmbientInclusion (single_injective pair_injective)
open ProetaleContinuousDirectImageMaps (functions)
open CuspNativeProperAdicPower (adic_scalar)
open OpenProetaleExtension (extensionByZero)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K]
  (m : ℕ) (hm : 2 ≤ m) (p : ℕ) (hp : Nat.Prime p) (hchar : CharP K p)
  (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)]

private abbrev f := projectiveMap K m hm
private abbrev j := affineOpen K
private abbrev s := smoothOpen K
private abbrev o := origin K
private abbrev z := infinityPoint K
private abbrev A := AddCommGrpCat.{1}

abbrev affineGroup := Sheaf.H ((extensionByZero (j K) A).obj
  (functions ℤ_[ℓ] (CuspProperCompactification.affineCusp K))) 2

abbrev smoothGroup := Sheaf.H ((extensionByZero (s K) A).obj
  (functions ℤ_[ℓ] (SmallEtaleGeometricBaseChange.cuspPuncturedOpen K).toScheme)) 2

/-- Actual native compact-support pullback on the affine cusp. -/
def affinePullback : affineGroup K ℓ →+ affineGroup K ℓ :=
  compactMap (f K m hm) (affineMap K m hm) (j K) (j K)
    (affine_isPullback K m hm).flip ℤ_[ℓ] 2

/-- Actual native compact-support pullback on the regular cusp locus. -/
def smoothPullback : smoothGroup K ℓ →+ smoothGroup K ℓ :=
  compactMap (f K m hm) (smoothMap K m hm) (s K) (s K)
    (smooth_isPullback K m hm).flip ℤ_[ℓ] 2

private theorem affine_quasiCompact : QuasiCompact (j K) := by
  letI : IsProper (projectiveCuspToBase K) := projectiveCusp_isProper K
  letI : QuasiCompact (j K ≫ projectiveCuspToBase K) := by
    rw [affineOpen_toBase]
    infer_instance
  exact QuasiCompact.of_comp (j K) (projectiveCuspToBase K)

include hp hchar in
set_option maxHeartbeats 7500000 in
/-- Actual compact pullback on the affine cusp is multiplication by the relative exponent. -/
theorem affine_scalar (x : affineGroup K ℓ) :
    affinePullback K m hm ℓ x = m • x := by
  letI : QuasiCompact (j K) := affine_quasiCompact K
  letI : IsClosedImmersion (z K) := infinityPoint_isClosedImmersion K
  have h : Set.range (j K) = (Set.range (z K))ᶜ := by
    rw [← CuspInfinitySupport.affine_complement_eq_infinity K, compl_compl]
  let a := Sheaf.H.map (ambient ℤ_[ℓ] (j K)) 2
  apply single_injective (j K) K ℓ (z K) h
  exact (ambient_naturality (f K m hm) (affineMap K m hm) (j K) (j K)
    (affine_isPullback K m hm).flip ℤ_[ℓ] 2 x).trans
    ((adic_scalar K m hm p hp hchar ℓ (a x)).trans (map_nsmul a m x).symm)

include hp hchar in
set_option maxHeartbeats 7500000 in
/-- Actual compact pullback on the regular cusp is multiplication by the relative exponent. -/
theorem smooth_scalar (x : smoothGroup K ℓ) :
    smoothPullback K m hm ℓ x = m • x := by
  letI : QuasiCompact (s K) := smoothOpen_quasiCompact K
  letI : IsClosedImmersion (o K) := properOrigin_closed K
  letI : IsClosedImmersion (z K) := infinityPoint_isClosedImmersion K
  let a := Sheaf.H.map (ambient ℤ_[ℓ] (s K)) 2
  apply pair_injective (s K) K ℓ (o K) (z K) (boundary_disjoint K) (smoothOpen_range K)
  exact (ambient_naturality (f K m hm) (smoothMap K m hm) (s K) (s K)
    (smooth_isPullback K m hm).flip ℤ_[ℓ] 2 x).trans
    ((adic_scalar K m hm p hp hchar ℓ (a x)).trans (map_nsmul a m x).symm)

end
end ManuscriptAudit.CuspNativeCompactAdicRelativePower

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``ManuscriptAudit.CuspNativeCompactAdicRelativePower.affine_scalar,
      ``ManuscriptAudit.CuspNativeCompactAdicRelativePower.smooth_scalar] do
    let ax ← collectAxioms n
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{n} depends on unexpected axioms {ax}"
    logInfo m!"{n} uses {ax}"
