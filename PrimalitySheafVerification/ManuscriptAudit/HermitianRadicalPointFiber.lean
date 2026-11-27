import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.FieldTheory.KummerExtension
import PrimalitySheafVerification.ManuscriptAudit.ComaximalIdealGrid
import PrimalitySheafVerification.ManuscriptAudit.HermitianTangentOrbit

/-! The extension of an actual point ideal is the product of its full coordinate orbit. -/

namespace ManuscriptAudit.HermitianRadicalPointFiber

open scoped BigOperators
open Polynomial RadicalCoordinateAlgebra HermitianTangentIdealMembership HermitianTangentOrbit

noncomputable section

variable {K : Type*} [Field K]

private def powerRoot {m : ℕ} [NeZero m] {z : K} (hz : IsPrimitiveRoot z m)
    (j : Fin m) : rootsOfUnity m K :=
  rootsOfUnity.mkOfPowEq (z ^ (j : ℕ)) (by rw [← pow_mul, mul_comm, pow_mul, hz.pow_eq_one, one_pow])

private theorem rootValue_powerRoot {m : ℕ} [NeZero m] {z : K} (hz : IsPrimitiveRoot z m)
    (j : Fin m) : rootValue (powerRoot hz j) = z ^ (j : ℕ) :=
  rootsOfUnity.coe_mkOfPowEq _

private def rootPowerEquiv {m : ℕ} [NeZero m] {z : K} (hz : IsPrimitiveRoot z m) :
    Fin m ≃ rootsOfUnity m K :=
  Equiv.ofBijective (powerRoot hz) ⟨by
    intro i j hij
    apply Fin.ext
    apply hz.pow_inj i.isLt j.isLt
    simpa only [rootValue_powerRoot] using congrArg rootValue hij, by
    intro x
    obtain ⟨j, hj, he⟩ := hz.eq_pow_of_pow_eq_one (rootValue_pow x)
    exact ⟨⟨j, hj⟩, rootValue_injective m ((rootValue_powerRoot hz ⟨j, hj⟩).trans he)⟩⟩

/-- The standard Kummer factorization evaluated in any commutative algebra. -/
theorem prod_root_differences {D : Type*} [CommRing D] [Algebra K D] (T : D)
    {m : ℕ} [NeZero m] [Fintype (rootsOfUnity m K)] {z : K}
    (hz : IsPrimitiveRoot z m) (u : K) :
    (∏ x : rootsOfUnity m K, T - algebraMap K D (rootValue x * u)) =
      T ^ m - algebraMap K D (u ^ m) := by
  have hp := X_pow_sub_C_eq_prod hz (NeZero.pos m) (show u ^ m = u ^ m from rfl)
  have he := congrArg (Polynomial.eval₂ (algebraMap K D) T) hp
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, eval₂_finsetProd] at he
  rw [he, Finset.prod_range]
  symm
  apply Fintype.prod_equiv (rootPowerEquiv hz)
  intro i
  change T - algebraMap K D (z ^ (i : ℕ) * u) =
    T - algebraMap K D (rootValue (powerRoot hz i) * u)
  rw [rootValue_powerRoot]

private theorem singleton_sup_is_top {D : Type*} [CommRing D] (T x y : D)
    (h : IsUnit (x - y)) :
    (Ideal.span ({T - x} : Set D)) ⊔ Ideal.span {T - y} = ⊤ := by
  let I : Ideal D := Ideal.span ({T - x} : Set D) ⊔ Ideal.span {T - y}
  change I = ⊤
  have hmem : x - y ∈ I := by
    rw [show x - y = (T - y) - (T - x) by ring]
    exact I.sub_mem ((le_sup_right : Ideal.span ({T - y} : Set D) ≤ I)
      (Ideal.mem_span_singleton_self _)) ((le_sup_left : Ideal.span ({T - x} : Set D) ≤ I)
      (Ideal.mem_span_singleton_self _))
  obtain ⟨e, he⟩ := h
  have hm : (e : D) ∈ I := he.symm ▸ hmem
  exact (Ideal.eq_top_iff_one I).mpr (by simpa using I.mul_mem_left (↑(e⁻¹) : D) hm)

private theorem roots_line_comaximal {D : Type*} [CommRing D] [Algebra K D]
    (T : D) {m : ℕ} {u : K} (hu : u ≠ 0) {x y : rootsOfUnity m K} (hxy : x ≠ y) :
    Ideal.span ({T - algebraMap K D (rootValue x * u)} : Set D) ⊔
      Ideal.span {T - algebraMap K D (rootValue y * u)} = ⊤ := by
  apply singleton_sup_is_top
  rw [← map_sub]
  apply IsUnit.map (algebraMap K D)
  apply isUnit_iff_ne_zero.mpr
  rw [sub_ne_zero, mul_left_inj' hu]
  exact fun h => hxy (rootValue_injective m h)

theorem pointIdeal_eq_sup {D : Type*} [CommRing D] (T S x y : D) :
    pointIdeal T S x y = Ideal.span {T - x} ⊔ Ideal.span {S - y} := by
  rw [pointIdeal, ← Ideal.span_union]
  congr 1
  ext w
  simp

variable {R : Type*} [CommRing R] [Algebra K R]
variable (m n : ℕ) [NeZero m] [NeZero n] (a b : R)

local notation "D₀" => DoubleExtension m n a b
local notation "U" => firstRoot m n a b
local notation "V" => secondRoot m n a b
local notation "i" => algebraMap K D₀
local notation "j" => algebraMap R D₀

/-- Extension of the normalized affine point ideal factors as the whole radical fiber. -/
theorem pointIdeal_map_eq_orbit [Fintype (rootsOfUnity m K)] [Fintype (rootsOfUnity n K)]
    {z w : K} (hz : IsPrimitiveRoot z m) (hw : IsPrimitiveRoot w n)
    {u v : K} (hu : u ≠ 0) (hv : v ≠ 0) :
    (pointIdeal a b (algebraMap K R (u ^ m)) (algebraMap K R (v ^ n))).map j =
      ∏ r : rootsOfUnity m K × rootsOfUnity n K,
        pointIdeal U V (i (rootValue r.1 * u)) (i (rootValue r.2 * v)) := by
  classical
  have hU : j a = U ^ m := (firstRoot_pow m n a b).symm
  have hV : j b = V ^ n := (secondRoot_pow m n a b).symm
  simp_rw [pointIdeal_eq_sup, Ideal.map_sup, Ideal.map_span, Set.image_singleton,
    map_sub, hU, hV, ← IsScalarTower.algebraMap_apply K R D₀]
  rw [Fintype.prod_prod_type']
  rw [ComaximalIdealGrid.prod_prod_sup_eq (s := Finset.univ) (t := Finset.univ)]
  · rw [Ideal.prod_span_singleton, Ideal.prod_span_singleton,
      prod_root_differences U hz, prod_root_differences V hw]
  · exact fun x _ y _ hxy => roots_line_comaximal U hu hxy
  · exact fun x _ y _ hxy => roots_line_comaximal V hv hxy

end
end ManuscriptAudit.HermitianRadicalPointFiber

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.HermitianRadicalPointFiber.prod_root_differences,
      ``ManuscriptAudit.HermitianRadicalPointFiber.pointIdeal_map_eq_orbit] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
