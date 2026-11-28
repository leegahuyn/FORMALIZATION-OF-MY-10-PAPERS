import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The dehomogenized Weierstrass equation at the point at infinity

In the Y=1 equation, write u=X/Y and v=Z/Y. Its equation is
v h=u³ with h(0,0)=1. The ideal (u,v) is consequently generated
by u on the open h≠0 containing the rational origin.
-/

namespace ManuscriptAudit.WeierstrassInfinityChartAlgebra

open Polynomial
open scoped Polynomial.Bivariate

universe u

noncomputable section

variable {K : Type u} [Field K] (W : WeierstrassCurve.Affine K)

/-- The factor of v in the equation in the standard Y chart. -/
def bracketPolynomial : K[X][Y] :=
  1 + C (C W.a₁ * X) + C (C W.a₃) * Y -
    C (C W.a₂ * X ^ 2) - C (C W.a₄ * X) * Y - C (C W.a₆) * Y ^ 2

/-- The original Weierstrass homogeneous cubic, dehomogenized at Y=1. -/
def equation : K[X][Y] :=
  Y * bracketPolynomial W - (C X) ^ 3

abbrev Ring := AdjoinRoot (equation W)

def x : Ring W := AdjoinRoot.mk (equation W) (C X)
def z : Ring W := AdjoinRoot.mk (equation W) Y
def bracket : Ring W := AdjoinRoot.mk (equation W) (bracketPolynomial W)

/-- In the actual quotient, v h=u³. -/
theorem relation : z W * bracket W = x W ^ 3 := by
  have hz : AdjoinRoot.mk (equation W) (equation W) = 0 := AdjoinRoot.mk_self
  apply sub_eq_zero.mp
  simpa only [equation, map_sub, map_pow, map_mul, x, z, bracket] using hz

/-- The rational point with the genuine affine coordinates u=v=0. -/
def origin : Ring W →ₐ[K] K :=
  AdjoinRoot.liftAlgHom (equation W) (Polynomial.aeval (0 : K)) 0 (by
    simp [equation])

theorem origin_x : origin W (x W) = 0 := by
  simp [origin, x]

theorem origin_z : origin W (z W) = 0 := by
  simp [origin, z]

theorem origin_bracket : origin W (bracket W) = 1 := by
  simp [origin, bracket, bracketPolynomial]

abbrev Neighborhood := Localization.Away (bracket W)

def localX : Neighborhood W := algebraMap (Ring W) (Neighborhood W) (x W)
def localZ : Neighborhood W := algebraMap (Ring W) (Neighborhood W) (z W)

private theorem local_relation :
    localZ W * algebraMap (Ring W) (Neighborhood W) (bracket W) = localX W ^ 3 := by
  simpa only [localX, localZ, map_mul, map_pow] using
    congrArg (algebraMap (Ring W) (Neighborhood W)) (relation W)

/-- Near the rational origin in the actual dehomogenized chart, its ideal
has the single parameter u as generator. -/
theorem local_originIdeal_principal :
    Ideal.span {localX W, localZ W} = Ideal.span ({localX W} : Set (Neighborhood W)) := by
  let I : Ideal (Neighborhood W) := Ideal.span {localX W}
  let h := algebraMap (Ring W) (Neighborhood W) (bracket W)
  have hh : IsUnit h := IsLocalization.Away.algebraMap_isUnit (bracket W)
  have hm : localZ W * h ∈ I := by
    rw [local_relation]
    exact Ideal.mem_span_singleton.mpr ⟨localX W ^ 2, by rw [pow_succ, mul_comm]⟩
  have hv : localZ W ∈ I := by
    obtain ⟨v, hv⟩ := hh
    have hmem := I.mul_mem_right (↑(v⁻¹) : Neighborhood W) (hv.symm ▸ hm)
    simpa only [mul_assoc, Units.mul_inv, mul_one] using hmem
  refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_mono ?_)
  · rw [Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨Ideal.subset_span (by simp), hv⟩
  · exact Set.singleton_subset_iff.mpr (by simp)

end

end ManuscriptAudit.WeierstrassInfinityChartAlgebra

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassInfinityChartAlgebra.relation,
      ``ManuscriptAudit.WeierstrassInfinityChartAlgebra.origin_x,
      ``ManuscriptAudit.WeierstrassInfinityChartAlgebra.origin_z,
      ``ManuscriptAudit.WeierstrassInfinityChartAlgebra.origin_bracket,
      ``ManuscriptAudit.WeierstrassInfinityChartAlgebra.local_originIdeal_principal] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
