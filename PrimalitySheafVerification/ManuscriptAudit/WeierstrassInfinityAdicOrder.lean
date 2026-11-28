import Lean.Util.CollectAxioms
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassInfinityDedekind
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassInfinityNormPole

/-! The discrete valuation at the actual rational Cartier point computes
the exact quotient degree of every nonzero affine Weierstrass function. -/

namespace ManuscriptAudit.WeierstrassInfinityAdicOrder

open WithZero WeierstrassCurve.Affine IsDedekindDomain
open WeierstrassInfinityChartAlgebra WeierstrassInfinityOriginIdeal
open WeierstrassInfinityPuncture WeierstrassInfinityOpenCover WeierstrassInfinityPoleCoordinates

noncomputable section

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
variable (W : WeierstrassCurve.Affine K) [W.IsElliptic]

private abbrev N := Neighborhood W
private abbrev P := Puncture W
private abbrev F := FractionRing (N W)

local instance : IsDedekindDomain (N W) :=
  WeierstrassInfinityDedekind.neighborhood_isDedekindDomain W

/-- The actual height-one prime of the rational point at infinity. -/
def infinityPrime : HeightOneSpectrum (N W) where
  asIdeal := Ideal.span {localX W}
  isPrime := (Ideal.span_singleton_prime (localX_prime W).ne_zero).mpr (localX_prime W)
  ne_bot := by
    rw [Ideal.span_singleton_eq_bot]
    exact (localX_prime W).ne_zero

private def punctureToLocalFractionField : P W →+* F W :=
  IsLocalization.Away.lift (localX W) (g := algebraMap (N W) (F W))
    (isUnit_iff_ne_zero.mpr (IsFractionRing.to_map_eq_zero_iff.not.mpr (localX_prime W).ne_zero))

/-- The genuine valuation at infinity on the actual punctured chart. -/
def punctureValuation : Valuation (P W) ℤᵐ⁰ :=
  ((infinityPrime W).valuation (F W)).comap (punctureToLocalFractionField W)

private theorem valuation_on_neighborhood (a : N W) :
    punctureValuation W (algebraMap (N W) (P W) a) = (infinityPrime W).intValuation a := by
  change (infinityPrime W).valuation (F W)
    (punctureToLocalFractionField W (algebraMap (N W) (P W) a)) = _
  rw [punctureToLocalFractionField, IsLocalization.Away.lift_eq,
    HeightOneSpectrum.valuation_of_algebraMap]

/-- The Cartier parameter at infinity has order exactly one. -/
theorem valuation_parameter : punctureValuation W (punctureX W) = exp (-1 : ℤ) := by
  rw [punctureX, valuation_on_neighborhood]
  exact (infinityPrime W).intValuation_singleton (localX_prime W).ne_zero rfl

/-- A section with nonzero residue at infinity has zero order there. -/
theorem valuation_nonzero_residue (a : N W) (ha : localOrigin W a ≠ 0) :
    punctureValuation W (algebraMap (N W) (P W) a) = 1 := by
  rw [valuation_on_neighborhood]
  apply HeightOneSpectrum.intValuation_eq_one_iff.mpr
  change a ∉ Ideal.span ({localX W} : Set (N W))
  rw [← localOrigin_ker]
  exact ha

/-- The pole at infinity of a nonzero affine function has the dimension
of its actual affine scheme of zeros, including multiplicities. -/
theorem valuation_affine_quotient_degree (f : W.CoordinateRing) (hf : f ≠ 0) :
    punctureValuation W (affineToPuncture W f) = exp
      (Module.finrank K (W.CoordinateRing ⧸ Ideal.span ({f} : Set W.CoordinateRing)) : ℤ) := by
  let d := Module.finrank K (W.CoordinateRing ⧸ Ideal.span ({f} : Set W.CoordinateRing))
  obtain ⟨a, ha, h⟩ := WeierstrassInfinityNormPole.exact_pole_degree_quotient W f hf
  have hv := congrArg (punctureValuation W) h
  rw [valuation_nonzero_residue W a ha, map_mul, map_pow, valuation_parameter,
    ← exp_nsmul] at hv
  change 1 = punctureValuation W (affineToPuncture W f) * exp (d • (-1 : ℤ)) at hv
  rw [nsmul_eq_mul, mul_neg, mul_one] at hv
  calc
    _ = punctureValuation W (affineToPuncture W f) * (exp (-(d : ℤ)) * exp (d : ℤ)) := by
      rw [← exp_add, neg_add_cancel, exp_zero, mul_one]
    _ = exp (d : ℤ) := by rw [← mul_assoc, ← hv, one_mul]

end

end ManuscriptAudit.WeierstrassInfinityAdicOrder

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassInfinityAdicOrder.infinityPrime,
      ``ManuscriptAudit.WeierstrassInfinityAdicOrder.valuation_parameter,
      ``ManuscriptAudit.WeierstrassInfinityAdicOrder.valuation_nonzero_residue,
      ``ManuscriptAudit.WeierstrassInfinityAdicOrder.valuation_affine_quotient_degree] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
