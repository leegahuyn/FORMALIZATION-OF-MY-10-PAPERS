import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.HermitianRootsOfUnity
import PrimalitySheafVerification.ManuscriptAudit.DoubleRadicalRotation
import PrimalitySheafVerification.ManuscriptAudit.HermitianTangentIdealMembership

/-! Descent of the product of Hermitian tangents over a complete coordinate orbit. -/

namespace ManuscriptAudit.HermitianTangentOrbit

open RadicalCoordinateAlgebra DoubleRadicalRotation HermitianTangentIdealMembership HermitianRootsOfUnity
open scoped BigOperators

noncomputable section

variable {K R : Type*} [Field K] [CommRing R] [Algebra K R] [Nontrivial R]
variable (m n : ℕ) [NeZero m] [NeZero n] (a b : R)

local notation "D₀" => DoubleExtension m n a b
local notation "U" => firstRoot m n a b
local notation "V" => secondRoot m n a b
local notation "i" => algebraMap K D₀

def familyTangent (q : ℕ) (u v : K)
    (x : rootsOfUnity m K) (y : rootsOfUnity n K) : D₀ :=
  tangent q U V (i (rootValue x * u)) (i (rootValue y * v))

private theorem familyTangent_eq {q : ℕ} {u v : K}
    (hm : m ∣ q + 1) (hn : n ∣ q + 1) (h : u ^ (q + 1) + v ^ (q + 1) = 1)
    (x : rootsOfUnity m K) (y : rootsOfUnity n K) :
    familyTangent m n a b q u v x y =
      i ((rootValue x * u) ^ q) * U + i ((rootValue y * v) ^ q) * V - 1 := by
  have he :
      (rootValue x * u) ^ (q + 1) + (rootValue y * v) ^ (q + 1) = 1 := by
    rw [mul_pow, mul_pow, pow_eq_one_of_order_dvd (rootValue_pow x) hm,
      pow_eq_one_of_order_dvd (rootValue_pow y) hn, one_mul, one_mul]
    exact h
  have hE := congrArg i he
  simp only [map_add, map_one, pow_succ, map_mul, map_pow] at hE
  simp only [familyTangent, tangent, map_mul, map_pow]
  linear_combination -hE

private theorem rotation_commutes_field (f : D₀ →ₐ[R] D₀) (x : K) :
    f (i x) = i x := by
  rw [IsScalarTower.algebraMap_apply K R D₀]
  exact f.commutes _

private theorem rotateFirst_reindex {q : ℕ} {u v : K} (hm : m ∣ q + 1)
    (hn : n ∣ q + 1) (h : u ^ (q + 1) + v ^ (q + 1) = 1)
    (z x : rootsOfUnity m K) (y : rootsOfUnity n K) :
    rotateFirst m n a b (rootValue z) (rootValue_pow z)
        (familyTangent m n a b q u v (z * x) y) =
      familyTangent m n a b q u v x y := by
  have hz : rootValue z ^ q * rootValue z = 1 := by
    rw [← pow_succ]
    exact pow_eq_one_of_order_dvd (rootValue_pow z) hm
  rw [familyTangent_eq m n a b hm hn h, familyTangent_eq m n a b hm hn h]
  simp only [map_sub, map_add, map_mul, map_one, rotation_commutes_field,
    rotateFirst_firstRoot, rotateFirst_secondRoot, rootValue_mul]
  have hScalar :
      i (rootValue z) ^ q * i (rootValue z) = 1 := by
    simpa only [map_mul, map_pow, map_one] using congrArg i hz
  simp only [mul_pow, map_mul, map_pow]
  calc
    _ = (i (rootValue z) ^ q * i (rootValue z)) *
        ((i (rootValue x) ^ q * i u ^ q) * U) +
        (i (rootValue y) ^ q * i v ^ q) * V - 1 := by ring
    _ = _ := by rw [hScalar, one_mul]

private theorem rotateSecond_reindex {q : ℕ} {u v : K} (hm : m ∣ q + 1)
    (hn : n ∣ q + 1) (h : u ^ (q + 1) + v ^ (q + 1) = 1)
    (x : rootsOfUnity m K) (w y : rootsOfUnity n K) :
    rotateSecond m n a b (rootValue w) (rootValue_pow w)
        (familyTangent m n a b q u v x (w * y)) =
      familyTangent m n a b q u v x y := by
  have hw : rootValue w ^ q * rootValue w = 1 := by
    rw [← pow_succ]
    exact pow_eq_one_of_order_dvd (rootValue_pow w) hn
  rw [familyTangent_eq m n a b hm hn h, familyTangent_eq m n a b hm hn h]
  simp only [map_sub, map_add, map_mul, map_one, rotation_commutes_field,
    rotateSecond_firstRoot, rotateSecond_secondRoot, rootValue_mul]
  have hScalar :
      i (rootValue w) ^ q * i (rootValue w) = 1 := by
    simpa only [map_mul, map_pow, map_one] using congrArg i hw
  simp only [mul_pow, map_mul, map_pow]
  calc
    _ = (i (rootValue x) ^ q * i u ^ q) * U +
        (i (rootValue w) ^ q * i (rootValue w)) *
        ((i (rootValue y) ^ q * i v ^ q) * V) - 1 := by ring
    _ = _ := by rw [hScalar, one_mul]

private def leftRotation {G : Type*} [Group G] (z : G) : G ≃ G where
  toFun x := z * x
  invFun x := z⁻¹ * x
  left_inv x := by simp
  right_inv x := by simp

/-- The product of tangents over the two full roots-of-unity groups comes from the base ring. -/
theorem exists_base_tangent_product [Fintype (rootsOfUnity m K)] [Fintype (rootsOfUnity n K)]
    {q : ℕ} {u v z w : K}
    (hm : m ∣ q + 1) (hn : n ∣ q + 1) (h : u ^ (q + 1) + v ^ (q + 1) = 1)
    (hz : IsPrimitiveRoot z m) (hw : IsPrimitiveRoot w n) :
    ∃ f : R, algebraMap R D₀ f =
      ∏ r : rootsOfUnity m K × rootsOfUnity n K, familyTangent m n a b q u v r.1 r.2 := by
  classical
  let t : rootsOfUnity m K × rootsOfUnity n K → D₀ :=
    fun r => familyTangent m n a b q u v r.1 r.2
  let x := rootsOfUnity.mkOfPowEq z hz.pow_eq_one
  let y := rootsOfUnity.mkOfPowEq w hw.pow_eq_one
  have hx : rootValue x = z := rootsOfUnity.coe_mkOfPowEq _
  have hy : rootValue y = w := rootsOfUnity.coe_mkOfPowEq _
  have hU : rotateFirst m n a b (rootValue x) (rootValue_pow x) (∏ r, t r) = ∏ r, t r := by
    rw [map_prod]
    symm
    apply Fintype.prod_equiv ((leftRotation x).prodCongr (Equiv.refl _))
    intro r
    exact (rotateFirst_reindex m n a b hm hn h x r.1 r.2).symm
  have hV : rotateSecond m n a b (rootValue y) (rootValue_pow y) (∏ r, t r) = ∏ r, t r := by
    rw [map_prod]
    symm
    apply Fintype.prod_equiv ((Equiv.refl _).prodCongr (leftRotation y))
    intro r
    exact (rotateSecond_reindex m n a b hm hn h r.1 y r.2).symm
  apply exists_base_of_fixed m n a b (NeZero.ne m) (NeZero.ne n) hz hw (∏ r, t r)
  · simpa only [hx] using hU
  · simpa only [hy] using hV

end
end ManuscriptAudit.HermitianTangentOrbit

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.HermitianTangentOrbit.exists_base_tangent_product] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
