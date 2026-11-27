import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicHermitianCoordinates
import PrimalitySheafVerification.ManuscriptAudit.CubicThreeTorsionOrdinate
import PrimalitySheafVerification.ManuscriptAudit.CubicHermitianFiniteInputs
import PrimalitySheafVerification.ManuscriptAudit.HermitianPrincipalDescent

/-! The Frobenius-square relation at points with both coordinates nonzero. -/

namespace ManuscriptAudit.CubicHermitianRegularPoints

open Polynomial WeierstrassCurve FiniteFieldPointCount
open CubicHermitianCoordinates CubicHermitianFiniteInputs
open HermitianPrincipalDescent AffinePointPrincipalRelation RadicalCoordinateAlgebra

noncomputable section

variable (E K : Type*) [Field E] [Fintype E] [Field K] [Algebra E K] [IsAlgClosed K] [DecidableEq K]

local notation "q" => Fintype.card E
local notation "Q" => (q * q)

/-- The principal divisor obtained from the Hermitian cover gives the native group relation. -/
theorem frobenius_product_relation {A : E} (hA : A ≠ 0)
    (hq3 : q % 3 = 2) (hq2 : q % 2 = 1)
    (hΔ : (shortCubic (0 : K) (algebraMap E K A)).Δ ≠ 0)
    {x y : K} (hx : x ≠ 0) (hy : y ≠ 0)
    (hP : (Centered (algebraMap E K A)).Nonsingular x y)
    (hP' : (Centered (algebraMap E K A)).Nonsingular (x ^ Q) (y ^ Q)) :
    q • (Affine.Point.some x y hP : (Centered (algebraMap E K A)).Point) +
      Affine.Point.some (x ^ Q) (y ^ Q) hP' = 0 := by
  classical
  let c := algebraMap E K A
  let R := (Centered c).CoordinateRing
  have hc : c ≠ 0 := by
    change algebraMap E K A ≠ 0
    simpa only [map_zero] using (algebraMap E K).injective.ne hA
  have hXY : y ^ 2 = x ^ 3 + c := by
    exact (CubicThreeTorsionOrdinate.nonsingular_iff hΔ x y).mp hP
  obtain ⟨α, β, hα, hβ, hαQ, hβQ⟩ := normalized_endpoint_scales E K hA hq3 hq2
  have hα₀ : α ≠ 0 := by
    intro hz
    apply hc
    simpa [c, hz] using hα.symm
  have hβ₀ : β ≠ 0 := by
    intro hz
    apply hc
    simpa [c, hz] using hβ.symm
  let m := (q + 1) / 3
  let n := (q + 1) / 2
  have hmQ : q + 1 = m * 3 := by dsimp only [m]; omega
  have hnQ : q + 1 = n * 2 := by dsimp only [n]; omega
  have hm₀ : 0 < m := by dsimp only [m]; omega
  have hn₀ : 0 < n := by dsimp only [n]; omega
  letI : NeZero m := ⟨hm₀.ne'⟩
  letI : NeZero n := ⟨hn₀.ne'⟩
  have hm : m ∣ q + 1 := ⟨3, hmQ⟩
  have hn : n ∣ q + 1 := ⟨2, hnQ⟩
  obtain ⟨z, hz⟩ := exists_primitive_root m (cast_divisor_add_one_ne_zero E K hm)
  obtain ⟨w, hw⟩ := exists_primitive_root n (cast_divisor_add_one_ne_zero E K hn)
  letI : Fintype (rootsOfUnity m K) := Fintype.ofFinite _
  letI : Fintype (rootsOfUnity n K) := Fintype.ofFinite _
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (α⁻¹ * x) hm₀
  obtain ⟨v, hv⟩ := IsAlgClosed.exists_pow_nat_eq (β⁻¹ * y) hn₀
  have hu₀ : u ≠ 0 := by
    intro h
    exact mul_ne_zero (inv_ne_zero hα₀) hx (by simpa [h, hm₀.ne'] using hu.symm)
  have hv₀ : v ≠ 0 := by
    intro h
    exact mul_ne_zero (inv_ne_zero hβ₀) hy (by simpa [h, hn₀.ne'] using hv.symm)
  let a : R := normalizedX c α
  let b : R := normalizedY c β
  let D := DoubleExtension m n a b
  let j : R →+* D := algebraMap R D
  letI : Algebra E D := ((algebraMap K D).comp (algebraMap E K)).toAlgebra
  have ha : a ^ 3 + b ^ 2 = 1 := normalized_coordinate_equation hc hα hβ
  have hU : firstRoot m n a b ^ (q + 1) = j (a ^ 3) := by
    rw [hmQ, pow_mul, firstRoot_pow, map_pow]
  have hV : secondRoot m n a b ^ (q + 1) = j (b ^ 2) := by
    rw [hnQ, pow_mul, secondRoot_pow, map_pow]
  have hHermitian : firstRoot m n a b ^ (q + 1) + secondRoot m n a b ^ (q + 1) = 1 := by
    rw [hU, hV, ← map_add, ha, map_one]
  have huQ : u ^ (q + 1) = (α⁻¹ * x) ^ 3 := by rw [hmQ, pow_mul, hu]
  have hvQ : v ^ (q + 1) = (β⁻¹ * y) ^ 2 := by rw [hnQ, pow_mul, hv]
  have hPoint : u ^ (q + 1) + v ^ (q + 1) = 1 := by
    rw [huQ, hvQ]
    simpa using normalized_equation (D := K) hc hα hβ (x := x) (y := y) (by simpa using hXY)
  obtain ⟨f, hf⟩ := exists_principal_frobenius_product E m n a b hm hn hz hw hu₀ hv₀ hHermitian hPoint
  have hu' : (u ^ Q) ^ m = α⁻¹ * x ^ Q := by
    rw [← pow_mul, Nat.mul_comm Q m, pow_mul, hu, mul_pow, inv_pow, hαQ]
  have hv' : (v ^ Q) ^ n = β⁻¹ * y ^ Q := by
    rw [← pow_mul, Nat.mul_comm Q n, pow_mul, hv, mul_pow, inv_pow, hβQ]
  rw [hu, hv, hu', hv', normalized_pointIdeal c hα₀ hβ₀ x y,
    normalized_pointIdeal c hα₀ hβ₀ (x ^ Q) (y ^ Q)] at hf
  exact nsmul_add_eq_zero_of_principal hP hP' q f hf

end
end ManuscriptAudit.CubicHermitianRegularPoints

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicHermitianRegularPoints.frobenius_product_relation
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
