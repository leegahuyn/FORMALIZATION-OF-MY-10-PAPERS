import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import PrimalitySheafVerification.ManuscriptAudit.AffineGenericQuotientCycles
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassProjectiveGenericQuotient
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassAffineCycleDegree
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassInfinityAdicOrder

/-! The degree of a section of the actual projective generic-unit
quotient is its finite affine divisor degree plus the coefficient at infinity. -/

namespace ManuscriptAudit.WeierstrassProjectiveCycleDegree

open AlgebraicGeometry CategoryTheory Opposite IsDedekindDomain
open WeierstrassProjectiveClosure WeierstrassCartierInfinity WeierstrassInfinityChartAlgebra
open WeierstrassProjectiveGenericPoint WeierstrassProjectiveGenericQuotient
open WeierstrassInfinityAdicOrder WeierstrassAffineCycleDegree AffineGenericQuotientCycles

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] [IsAlgClosed K] (W : WeierstrassCurve.Affine K) [W.IsElliptic]

private abbrev N := Neighborhood W
private abbrev P := (quotient W).obj.obj (op (terminal W))

local instance : IsOpenImmersion (neighborhoodOpen W) := neighborhoodOpen_isOpenImmersion W
local instance : IsDedekindDomain W.CoordinateRing := WeierstrassAffineDedekind.coordinateRing_isDedekindDomain W
local instance : IsDedekindDomain (N W) := WeierstrassInfinityDedekind.neighborhood_isDedekindDomain W
local instance : Algebra (N W) W.FunctionField := neighborhoodFractionAlgebra W
local instance : IsFractionRing (N W) W.FunctionField := neighborhood_isFractionRing W

local instance : Algebra.FiniteType K W.CoordinateRing :=
  inferInstanceAs (Algebra.FiniteType K (AdjoinRoot W.polynomial))

local instance : Algebra.FiniteType K (N W) :=
  inferInstanceAs (Algebra.FiniteType K (Localization.Away (bracket W)))

/-- The actual finite divisor cycle on the genuine affine chart. -/
def affineCycle : P W →+ (HeightOneSpectrum W.CoordinateRing →₀ ℤ) :=
  ambientSectionsToCycle K W.CoordinateRing W.FunctionField (affineOpen W) (genericPoint W) rfl

/-- The actual finite divisor cycle on the genuine infinity neighborhood. -/
def neighborhoodCycle : P W →+ (HeightOneSpectrum (N W) →₀ ℤ) :=
  ambientSectionsToCycle K (N W) W.FunctionField (neighborhoodOpen W) (genericPoint W)
    (genericPoint_factors_infinity W)

/-- The genuine coefficient of the unique point at infinity. -/
def infinityMultiplicity : (HeightOneSpectrum (N W) →₀ ℤ) →+ ℤ where
  toFun d := d (infinityPrime W)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The genuine signed degree of a global section of the native quotient. -/
def sectionDegree : P W →+ ℤ :=
  ((cycleDegree W).comp (affineCycle W)) + ((infinityMultiplicity W).comp (neighborhoodCycle W))

end

end ManuscriptAudit.WeierstrassProjectiveCycleDegree

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassProjectiveCycleDegree.affineCycle,
      ``ManuscriptAudit.WeierstrassProjectiveCycleDegree.neighborhoodCycle,
      ``ManuscriptAudit.WeierstrassProjectiveCycleDegree.sectionDegree] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
