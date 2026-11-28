import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import PrimalitySheafVerification.ManuscriptAudit.DedekindFractionalCycleEquiv
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassFractionalIdealDegree

/-! The degree on actual finite affine divisor cycles is the degree of
their uniquely corresponding nonzero fractional ideals. -/

namespace ManuscriptAudit.WeierstrassAffineCycleDegree

open IsDedekindDomain DedekindPrincipalDivisor DedekindFractionalCycleEquiv
open WeierstrassFractionalIdealDegree
open scoped nonZeroDivisors

noncomputable section

universe u
variable {K : Type u} [Field K] [IsAlgClosed K] (W : WeierstrassCurve.Affine K) [W.IsElliptic]

private abbrev A := W.CoordinateRing
private abbrev F := W.FunctionField
private abbrev I := FractionalIdeal (A W)⁰ (F W)

local instance : IsDedekindDomain (A W) := WeierstrassAffineDedekind.coordinateRing_isDedekindDomain W

private def degreeOnUnits : Additive (I W)ˣ →+ ℤ where
  toFun a := fractionalDegree W a.toMul.val
  map_zero' := by
    change fractionalDegree W (1 : I W) = 0
    have h := fractionalDegree_mul W (1 : I W) 1 one_ne_zero one_ne_zero
    rw [one_mul] at h
    omega
  map_add' a b := fractionalDegree_mul W _ _ a.toMul.ne_zero b.toMul.ne_zero

/-- The signed total degree of a finite native affine divisor cycle. -/
def cycleDegree : (HeightOneSpectrum (A W) →₀ ℤ) →+ ℤ :=
  (degreeOnUnits W).comp (cycleEquiv (A W) (F W)).symm.toAddMonoidHom

theorem cycleDegree_principal (x : Additive (F W)ˣ) :
    cycleDegree W (principalDivisor (A W) (F W) x) =
      fractionalDegree W (FractionalIdeal.spanSingleton (A W)⁰ (x.toMul : F W)) := by
  change degreeOnUnits W ((cycleEquiv (A W) (F W)).symm (principalDivisor (A W) (F W) x)) = _
  rw [cycleEquiv_principal]
  rfl

end

end ManuscriptAudit.WeierstrassAffineCycleDegree

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.WeierstrassAffineCycleDegree.cycleDegree_principal
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
