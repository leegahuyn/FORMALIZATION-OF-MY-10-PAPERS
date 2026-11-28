import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeProperPowerKummerScalar
import PrimalitySheafVerification.ManuscriptAudit.ProetaleFreeTerminalPullback
import PrimalitySheafVerification.ManuscriptAudit.ProetaleKummerSchemeConstant
import PrimalitySheafVerification.ManuscriptAudit.ProetaleSchemeConstantNaturality

/-! The actual relative power pulls back ordinary proper cusp cohomology
with finite cyclic coefficients by multiplication by its exponent. -/

namespace ManuscriptAudit.CuspNativeProperFinitePower

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open CuspProperCompactification (projectiveCusp projectiveCuspToBase)
open CuspRelativePowerMap (projectiveMap projectiveMap_overField)
open CuspNativeRelativePowerBoundary (relativeTerminalIso)
open CuspNativeProperPowerKummerScalar (properMap finite_scalar)
open ProetaleFreeTerminalPullback (map_terminal)
open ProetaleKummerPower (power J G)
open ProetaleKummerSequence (constantKernelIso)
open ProetaleKummerCoefficientMap (coefficientGroup)
open ProetaleKummerSchemePullback (kernelMap kernelPullback)
open ProetaleKummerSchemeConstant (constant_cohomology)
open ProetaleSchemeCohomologyPullback (constant)
open ProetaleSchemeConstantNaturality (constant_natural)
open ProetaleCohomologyIso (cohomologyIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K]
  (m : ℕ) (hm : 2 ≤ m) (p : ℕ) (hp : Nat.Prime p) (hchar : CharP K p)
  (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)]

private abbrev X := projectiveCusp K
private abbrev f := projectiveMap K m hm
private abbrev k := projectiveCuspToBase K
private abbrev C := constantSheaf (J (X K)) G
private abbrev d (r : ℕ) := ℓ ^ r

local instance order_neZero (r : ℕ) : NeZero (d ℓ r) :=
  ⟨pow_ne_zero r (show ℓ.Prime from Fact.out).ne_zero⟩
local instance cast_power_neZero (r : ℕ) : NeZero ((d ℓ r : ℕ) : K) :=
  ⟨by rw [Nat.cast_pow]; exact pow_ne_zero r (NeZero.ne (ℓ : K))⟩

private abbrev M (r : ℕ) := coefficientGroup K (d ℓ r)
private abbrev N (r : ℕ) := AddCommGrpCat.of (ULift.{1} (ZMod (d ℓ r)))

include hp hchar in
set_option maxHeartbeats 6500000 in
/-- The actual, ordinary derived functor comparison on proper Kummer H² is scalar. -/
theorem kernel_scalar (r : ℕ)
    (x : Sheaf.H (CategoryTheory.Limits.kernel (power (X K) (d ℓ r))) 2) :
    kernelMap (f K m hm) (d ℓ r) 2 x = m • x := by
  have h := map_terminal (f K m hm) (relativeTerminalIso K m hm)
    (kernelPullback (f K m hm) (d ℓ r)) 2 x
  change properMap K m hm (d ℓ r) x = kernelMap (f K m hm) (d ℓ r) 2 x at h
  exact h.symm.trans (finite_scalar K m hm p hp hchar ℓ r x)

include hp hchar in
set_option maxHeartbeats 6600000 in
theorem roots_scalar (r : ℕ) (x : Sheaf.H ((C K).obj (M K ℓ r)) 2) :
    constant (f K m hm) (M K ℓ r) 2 x = m • x := by
  let e := cohomologyIso (constantKernelIso (k K) (d ℓ r)) 2
  apply e.injective
  have h := constant_cohomology (d ℓ r) (f K m hm) (k K) (k K)
    (projectiveMap_overField K m hm) 2 x
  change kernelMap (f K m hm) (d ℓ r) 2 (e x) =
    e (constant (f K m hm) (M K ℓ r) 2 x) at h
  exact h.symm.trans ((kernel_scalar K m hm p hp hchar ℓ r (e x)).trans (map_nsmul e m x).symm)

include hp hchar in
set_option maxHeartbeats 7000000 in
/-- Actual proper cohomological pullback on constant ZMod (ℓ^r) is multiplication by m. -/
theorem finite_scalar (r : ℕ) (x : Sheaf.H ((C K).obj (N ℓ r)) 2) :
    constant (f K m hm) (N ℓ r) 2 x = m • x := by
  let root := (CuspRootCoefficients.rootsOfUnityEquivZMod K (d ℓ r)).toAdditive
  let i : M K ℓ r ≅ N ℓ r := (AddEquiv.ulift.trans (root.trans AddEquiv.ulift.symm)).toAddCommGrpIso
  let e := cohomologyIso ((C K).mapIso i) 2
  obtain ⟨y, rfl⟩ := e.surjective x
  have h := constant_natural (f K m hm) i.hom 2 y
  change constant (f K m hm) (N ℓ r) 2 (e y) =
    e (constant (f K m hm) (M K ℓ r) 2 y) at h
  exact h.trans ((congrArg e (roots_scalar K m hm p hp hchar ℓ r y)).trans (map_nsmul e m y))

end
end ManuscriptAudit.CuspNativeProperFinitePower

open Lean Elab Command in
run_cmd do
  let n := ``ManuscriptAudit.CuspNativeProperFinitePower.finite_scalar
  let ax ← collectAxioms n
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{n} depends on unexpected axioms {ax}"
  logInfo m!"{n} uses {ax}"
