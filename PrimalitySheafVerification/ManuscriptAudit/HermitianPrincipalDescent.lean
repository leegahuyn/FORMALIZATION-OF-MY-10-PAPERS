import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffinePointPrincipalRelation
import PrimalitySheafVerification.ManuscriptAudit.HermitianRadicalPointFiber
import PrimalitySheafVerification.ManuscriptAudit.HermitianTangentOrbit
import PrimalitySheafVerification.ManuscriptAudit.HermitianTangentIdeal

/-! A product of tangent divisors descends through the actual finite free radical extension. -/

namespace ManuscriptAudit.HermitianPrincipalDescent

open scoped BigOperators
open RadicalCoordinateAlgebra HermitianTangentIdealMembership HermitianTangentIdeal
open HermitianTangentOrbit HermitianRadicalPointFiber AffinePointPrincipalRelation HermitianRootsOfUnity

noncomputable section

variable {K : Type*} [Field K]

theorem rootValue_frobenius_sq {m q : ℕ} (hm : m ∣ q + 1) (z : rootsOfUnity m K) :
    rootValue z ^ (q * q) = rootValue z := by
  have hz : rootValue z ^ q * rootValue z = 1 := by
    rw [← pow_succ]
    exact pow_eq_one_of_order_dvd (rootValue_pow z) hm
  apply mul_right_cancel₀ (pow_ne_zero q (rootValue_ne_zero z))
  calc
    _ = (rootValue z ^ q * rootValue z) ^ q := by rw [pow_mul, mul_pow]
    _ = 1 := by rw [hz, one_pow]
    _ = _ := by rw [mul_comm, hz]

private theorem conjugate_or_comaximal {D : Type*} [CommRing D] [Algebra K D]
    (U V : D) (q : ℕ) (x y : K) :
    (algebraMap K D x ^ (q * q) = algebraMap K D x ∧
      algebraMap K D y ^ (q * q) = algebraMap K D y) ∨
    pointIdeal U V (algebraMap K D x) (algebraMap K D y) ⊔
      pointIdeal U V (algebraMap K D x ^ (q * q)) (algebraMap K D y ^ (q * q)) = ⊤ := by
  by_cases hx : x ^ (q * q) = x
  · by_cases hy : y ^ (q * q) = y
    · exact Or.inl ⟨by rw [← map_pow, hx], by rw [← map_pow, hy]⟩
    · right
      apply pointIdeal_sup_eq_top
      right
      rw [← map_pow, ← map_sub]
      exact (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (fun h => hy h.symm))).map (algebraMap K D)
  · right
    apply pointIdeal_sup_eq_top
    left
    rw [← map_pow, ← map_sub]
    exact (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (fun h => hx h.symm))).map (algebraMap K D)

variable (E : Type*) [Field E] [Fintype E]
variable {R : Type*} [CommRing R] [Algebra K R] [Nontrivial R]
variable (m n : ℕ) [NeZero m] [NeZero n] (a b : R)

local notation "q" => Fintype.card E
local notation "D₀" => DoubleExtension m n a b
local notation "U" => firstRoot m n a b
local notation "V" => secondRoot m n a b
local notation "i" => algebraMap K D₀
local notation "j" => algebraMap R D₀

/-- The product of the normalized point ideal to power q and its q²-Frobenius mate is principal. -/
theorem exists_principal_frobenius_product [Algebra E D₀]
    [Fintype (rootsOfUnity m K)] [Fintype (rootsOfUnity n K)]
    (hm : m ∣ q + 1) (hn : n ∣ q + 1)
    {z w u v : K} (hz : IsPrimitiveRoot z m) (hw : IsPrimitiveRoot w n)
    (hu : u ≠ 0) (hv : v ≠ 0)
    (hHermitian : U ^ (q + 1) + V ^ (q + 1) = 1)
    (hPoint : u ^ (q + 1) + v ^ (q + 1) = 1) :
    ∃ f : R,
      pointIdeal a b (algebraMap K R (u ^ m)) (algebraMap K R (v ^ n)) ^ q *
      pointIdeal a b (algebraMap K R ((u ^ (q * q)) ^ m))
        (algebraMap K R ((v ^ (q * q)) ^ n)) = Ideal.span {f} := by
  classical
  letI := double_faithfullyFlat m n a b (NeZero.ne m) (NeZero.ne n)
  let Ω := rootsOfUnity m K × rootsOfUnity n K
  let t : Ω → D₀ := fun r => familyTangent m n a b q u v r.1 r.2
  let J : Ω → Ideal D₀ := fun r => pointIdeal U V (i (rootValue r.1 * u)) (i (rootValue r.2 * v))
  let J' : Ω → Ideal D₀ := fun r => pointIdeal U V
    (i (rootValue r.1 * u ^ (q * q))) (i (rootValue r.2 * v ^ (q * q)))
  obtain ⟨f, hf⟩ := exists_base_tangent_product m n a b hm hn hPoint hz hw
  refine ⟨f, ideal_product_principal_of_faithfullyFlat (S := D₀) _ _ q f ?_⟩
  have hTang (r : Ω) : Ideal.span {t r} = J r ^ q * J' r := by
    let x := rootValue r.1 * u
    let y := rootValue r.2 * v
    have hxy : x ^ (q + 1) + y ^ (q + 1) = 1 := by
      dsimp only [x, y]
      rw [mul_pow, mul_pow, pow_eq_one_of_order_dvd (rootValue_pow r.1) hm,
        pow_eq_one_of_order_dvd (rootValue_pow r.2) hn, one_mul, one_mul]
      exact hPoint
    have hi : (i x) ^ (q + 1) + (i y) ^ (q + 1) = 1 := by
      simpa only [map_add, map_pow, map_one] using congrArg i hxy
    have hy : IsUnit (i y) :=
      (isUnit_iff_ne_zero.mpr (mul_ne_zero (rootValue_ne_zero r.2) hv)).map i
    have h := tangent_ideal_eq E hHermitian hi hy (conjugate_or_comaximal U V q x y)
    have hx' : (i x) ^ (q * q) = i (rootValue r.1 * u ^ (q * q)) := by
      rw [← map_pow, show x = rootValue r.1 * u from rfl, mul_pow, rootValue_frobenius_sq hm]
    have hy' : (i y) ^ (q * q) = i (rootValue r.2 * v ^ (q * q)) := by
      rw [← map_pow, show y = rootValue r.2 * v from rfl, mul_pow, rootValue_frobenius_sq hn]
    rw [hx', hy'] at h
    exact h
  have hFirst := pointIdeal_map_eq_orbit m n a b hz hw hu hv
  have hSecond := pointIdeal_map_eq_orbit m n a b hz hw (pow_ne_zero (q * q) hu) (pow_ne_zero (q * q) hv)
  rw [hFirst, hSecond, hf]
  change (∏ r, J r) ^ q * (∏ r, J' r) = Ideal.span {∏ r, t r}
  have hPow : (∏ r, J r) ^ q = ∏ r, J r ^ q :=
    map_prod (powMonoidHom q) J Finset.univ
  rw [hPow, ← Finset.prod_mul_distrib, ← Ideal.prod_span_singleton]
  exact Finset.prod_congr rfl (fun r _ => (hTang r).symm)

end
end ManuscriptAudit.HermitianPrincipalDescent

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.HermitianPrincipalDescent.rootValue_frobenius_sq,
      ``ManuscriptAudit.HermitianPrincipalDescent.exists_principal_frobenius_product] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
