import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeRelativePowerBoundary
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeLaurentFreeKummerPower
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeAdicHTwoPositiveCharacteristic

/-! The proper native cusp Kummer class has scalar relative power action.
The Mayer–Vietoris boundary transfers the actual Laurent exponent onto it. -/

namespace ManuscriptAudit.CuspNativeProperPowerKummerScalar

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CuspProperCompactification (projectiveCusp projectiveCuspToBase affineCusp affineOpen)
open CuspProperYChart (lineOpen)
open CuspNativeProetaleHTwoLower (cover)
open CuspLaurentNativeCoverGeometry (inclusion first second native_isPullback)
open CuspRelativePowerMap (projectiveMap)
open CuspNativeRelativePowerBoundary (complex relativeOverlapIso relativeTerminalIso)
open ProetaleMayerVietorisConnecting (firstEquiv lastEquiv connecting_surjective)
open ProetaleMayerVietorisSite (coverComplex_shortExact)
open ProetaleInverseImage (inverseImage)
open ProetaleKummerPower (power)
open ProetaleKummerSequence (constantKernelIso)
open ProetaleKummerSchemePullback (kernelPullback)
open ProetaleKummerCoefficientMap (coefficientGroup)
open ProetaleOpenRestriction (restrictionConstantIso)
open ProetaleCohomologyIso (cohomologyIso)
open OpenProetaleExtension (restriction)
open ProetaleConstantRestriction (constant)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K]

private abbrev X := projectiveCusp K
private abbrev j := affineOpen K
private abbrev k := lineOpen K
private abbrev l := inclusion K
private abbrev H := coverComplex_shortExact (j K) (k K) (l K) (first K) (second K)
  (native_isPullback K) (cover K)
private abbrev A := AddCommGrpCat.{1}

variable (m : ℕ) (hm : 2 ≤ m)

private abbrev f := projectiveMap K m hm

variable (d : ℕ) [NeZero (d : K)]

local instance order_neZero : NeZero d := NeZero.of_neZero_natCast K

private abbrev F := kernel (power (X K) d)
private abbrev overlapAlg := (complex K).X₁
private abbrev terminalAlg := (complex K).X₃

private abbrev delta : Ext (overlapAlg K) (F K d) 1 →+ Ext (terminalAlg K) (F K d) 2 :=
  (H K).extClass.precomp (F K d) rfl

private abbrev mapOverlap :=
  ProetaleFreeExtPullback.map (f K m hm) (relativeOverlapIso K m hm)
    (kernelPullback (f K m hm) d) 1

private abbrev mapTerminal :=
  ProetaleFreeExtPullback.map (f K m hm) (relativeTerminalIso K m hm)
    (kernelPullback (f K m hm) d) 2

set_option maxHeartbeats 6300000 in
private theorem boundary_compat (x : Ext (overlapAlg K) (F K d) 1) :
    mapTerminal K m hm d (delta K d x) = delta K d (mapOverlap K m hm d x) := by
  let L := inverseImage (f K m hm)
  let g := kernelPullback (f K m hm) d
  let p := (ProetaleFreeExtPullback.chartIso (f K m hm) (relativeOverlapIso K m hm)).inv
  let q := (ProetaleFreeExtPullback.chartIso (f K m hm) (relativeTerminalIso K m hm)).inv
  have h := CuspNativeRelativePowerBoundary.map_boundary K m hm (F K d) 1 x
  dsimp only at h
  rw [CuspNativeRelativePowerBoundary.comparison_inv_first,
    CuspNativeRelativePowerBoundary.comparison_inv_last] at h
  change (Ext.mk₀ q).comp (((H K).extClass.comp x rfl).mapExactFunctor L) rfl =
    (H K).extClass.comp ((Ext.mk₀ p).comp (x.mapExactFunctor L) rfl) rfl at h
  change ((Ext.mk₀ q).comp (((H K).extClass.comp x rfl).mapExactFunctor L) rfl).comp
      (Ext.mk₀ g) rfl =
    (H K).extClass.comp (((Ext.mk₀ p).comp (x.mapExactFunctor L) rfl).comp (Ext.mk₀ g) rfl) rfl
  rw [h, Ext.comp_assoc_of_third_deg_zero]

private theorem delta_surjective
    (hU : Subsingleton (Sheaf.H ((restriction (j K) A).obj (F K d)) 2))
    (hV : Subsingleton (Sheaf.H ((restriction (k K) A).obj (F K d)) 2)) :
    Function.Surjective (delta K d) := by
  let e := firstEquiv (j K) (k K) (l K) (first K) (second K) (native_isPullback K)
    (cover K) (F K d) 1
  let b := lastEquiv (j K) (k K) (l K) (first K) (second K) (native_isPullback K)
    (cover K) (F K d) 2
  let h := connecting_surjective (j K) (k K) (l K) (first K) (second K) (native_isPullback K)
    (cover K) (F K d) 1 hU hV
  intro y
  obtain ⟨u, hu⟩ := h (b y)
  exact ⟨e.symm u, b.injective hu⟩

/-- The terminal free term is the ordinary native H² of the proper cusp. -/
abbrev terminalEquiv :=
  lastEquiv (j K) (k K) (l K) (first K) (second K) (native_isPullback K)
    (cover K) (F K d) 2

/-- The actual scheme pullback implemented using the terminal free representable. -/
def properMap : Sheaf.H (F K d) 2 →+ Sheaf.H (F K d) 2 :=
  (terminalEquiv K d).toAddMonoidHom.comp
    ((mapTerminal K m hm d).comp (terminalEquiv K d).symm.toAddMonoidHom)

set_option maxHeartbeats 6700000 in
theorem proper_scalar_of_chart_vanishing
    (hU : Subsingleton (Sheaf.H ((restriction (j K) A).obj (F K d)) 2))
    (hV : Subsingleton (Sheaf.H ((restriction (k K) A).obj (F K d)) 2))
    (x : Sheaf.H (F K d) 2) :
    properMap K m hm d x = m • x := by
  let b := terminalEquiv K d
  obtain ⟨u, hu⟩ := delta_surjective K d hU hV (b.symm x)
  have hu' : b (delta K d u) = x := (congrArg b hu).trans (b.apply_symm_apply x)
  have h : mapOverlap K m hm d u = m • u :=
    CuspNativeLaurentFreeKummerPower.kernel_scalar K m hm d u
  change b (mapTerminal K m hm d (b.symm x)) = m • x
  rw [← hu, boundary_compat, h, map_nsmul, map_nsmul, hu']

variable (p : ℕ) (hp : Nat.Prime p) (hchar : CharP K p)
variable (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)]

local instance cast_power_neZero (r : ℕ) : NeZero ((ℓ ^ r : ℕ) : K) :=
  ⟨by rw [Nat.cast_pow]; exact pow_ne_zero _ (NeZero.ne (ℓ : K))⟩

private def kernelConstant (r : ℕ) :
    F K (ℓ ^ r) ≅ constant (X K) (ZMod (ℓ ^ r)) := by
  let s := (CuspRootCoefficients.rootsOfUnityEquivZMod K (ℓ ^ r)).toAdditive
  let e : coefficientGroup K (ℓ ^ r) ≅ AddCommGrpCat.of (ULift.{1} (ZMod (ℓ ^ r))) :=
    (AddEquiv.ulift.trans (s.trans AddEquiv.ulift.symm)).toAddCommGrpIso
  exact (constantKernelIso (projectiveCuspToBase K) (ℓ ^ r)).symm ≪≫
    (constantSheaf (Scheme.ProEt.topology (X K)) A).mapIso e

include hp hchar in
set_option maxHeartbeats 8500000 in
/-- At every actual finite prime-power level the proper Kummer H² pullback is m. -/
theorem finite_scalar (r : ℕ) (x : Sheaf.H (F K (ℓ ^ r)) 2) :
    properMap K m hm (ℓ ^ r) x = m • x := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : CharP K p := hchar
  let R := ZMod (ℓ ^ r)
  let M := AddCommGrpCat.of (ULift.{1} R)
  let V := Spec (CommRingCat.of (Polynomial K))
  let T := affineCusp K
  letI : Subsingleton (Sheaf.H (ProetaleAdicHOneDetection.finiteCoefficient V ℓ r) 2) :=
    AffineLineNativeResidueHTwo.native_residue_HTwo_subsingleton K ℓ r
  let q := cohomologyIso (ProetaleDiscreteConstant.nativeResidueIso V ℓ r) 2
  letI : Subsingleton (Sheaf.H (constant V R) 2) := q.injective.subsingleton
  let a := cohomologyIso (((restriction (j K) A).mapIso (kernelConstant K ℓ r)) ≪≫
    (restrictionConstantIso (j K)).app M) 2
  let b := cohomologyIso (((restriction (k K) A).mapIso (kernelConstant K ℓ r)) ≪≫
    (restrictionConstantIso (k K)).app M) 2
  let c := CuspProetaleCohomologyEquivalence.cyclicEquiv K p (ℓ ^ r) 2
  letI : Subsingleton (Sheaf.H (constant T R) 2) := c.injective.subsingleton
  exact proper_scalar_of_chart_vanishing K m hm (ℓ ^ r)
    a.injective.subsingleton b.injective.subsingleton x

end
end ManuscriptAudit.CuspNativeProperPowerKummerScalar

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``ManuscriptAudit.CuspNativeProperPowerKummerScalar.proper_scalar_of_chart_vanishing,
      ``ManuscriptAudit.CuspNativeProperPowerKummerScalar.finite_scalar] do
    let ax ← collectAxioms n
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{n} depends on unexpected axioms {ax}"
    logInfo m!"{n} uses {ax}"
