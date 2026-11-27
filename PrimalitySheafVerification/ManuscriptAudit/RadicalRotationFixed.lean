import Lean.Util.CollectAxioms
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic.LinearCombination
import PrimalitySheafVerification.ManuscriptAudit.RadicalCoordinateAlgebra

/-! A primitive scalar rotation fixes exactly the scalars of a monomial-root algebra. -/

namespace ManuscriptAudit.RadicalRotationFixed

open Polynomial Module RadicalCoordinateAlgebra

noncomputable section

variable {K R : Type*} [Field K] [CommRing R] [Algebra K R]

def rotation (m : ℕ) (a : R) (z : K) (hz : z ^ m = 1) :
    Extension m a →ₐ[R] Extension m a :=
  lift m a (algebraMap K (Extension m a) z * root m a) (by
    rw [mul_pow, ← map_pow, hz, map_one, one_mul, root_pow])

@[simp] theorem rotation_root (m : ℕ) (a : R) (z : K) (hz : z ^ m = 1) :
    rotation m a z hz (root m a) = algebraMap K (Extension m a) z * root m a := by
  unfold rotation
  rw [lift_root]

variable [Nontrivial R]

/-- A fixed element descends to the coefficient ring. -/
theorem exists_scalar_of_fixed (m : ℕ) (a : R) (hm : m ≠ 0) (z : K) (hz : IsPrimitiveRoot z m)
    (t : Extension m a) (h : rotation m a z hz.pow_eq_one t = t) :
    ∃ r : R, algebraMap R (Extension m a) r = t := by
  classical
  let A := Extension m a
  let B := basis m a hm
  let e := rotation m a z hz.pow_eq_one
  let c := algebraMap K R z
  have hFixed : e t = t := h
  have hBasis (i : Fin m) : e (B i) = c ^ (i : ℕ) • B i := by
    have hB : B i = root m a ^ (i : ℕ) := basis_apply m a hm i
    rw [hB, map_pow]
    change (rotation m a z hz.pow_eq_one (root m a)) ^ (i : ℕ) = _
    rw [rotation_root, mul_pow, Algebra.smul_def]
    change _ = algebraMap R A ((algebraMap K R z) ^ (i : ℕ)) * root m a ^ (i : ℕ)
    rw [map_pow, ← IsScalarTower.algebraMap_apply K R A]
  have he : e t = ∑ i : Fin m, (B.repr t i * c ^ (i : ℕ)) • B i := by
    calc
      _ = e (∑ i : Fin m, B.repr t i • B i) := congrArg e (B.sum_repr t).symm
      _ = _ := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [map_smul e, hBasis, smul_smul]
  have hCoeff (i : Fin m) : B.repr t i = B.repr t i * c ^ (i : ℕ) := by
    have h := congrArg (fun x : A => B.repr x i) (hFixed.symm.trans he)
    exact h.trans (congrFun (B.repr_sum_self (fun j : Fin m => B.repr t j * c ^ (j : ℕ))) i)
  have hZero (i : Fin m) (hi : (i : ℕ) ≠ 0) : B.repr t i = 0 := by
    have hn : z ^ (i : ℕ) ≠ 1 := hz.pow_ne_one_of_pos_of_lt hi i.isLt
    have hUnit : IsUnit (c ^ (i : ℕ) - 1) := by
      change IsUnit ((algebraMap K R z) ^ (i : ℕ) - 1)
      rw [← map_pow, ← map_one (algebraMap K R), ← map_sub]
      exact (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hn)).map (algebraMap K R)
    apply hUnit.mul_left_injective
    rw [zero_mul]
    linear_combination -(hCoeff i)
  let i₀ : Fin m := ⟨0, Nat.pos_of_ne_zero hm⟩
  have hSum : (∑ i : Fin m, B.repr t i • B i) = B.repr t i₀ • B i₀ := by
    apply Finset.sum_eq_single i₀
    · intro i _ hi
      rw [hZero i (fun he => hi (Fin.ext he)), zero_smul]
    · simp
  have hI : B i₀ = 1 := (basis_apply m a hm i₀).trans (pow_zero _)
  have hT : t = B.repr t i₀ • B i₀ := (B.sum_repr t).symm.trans hSum
  rw [hI, Algebra.smul_def, mul_one] at hT
  exact ⟨B.repr t i₀, hT.symm⟩

end
end ManuscriptAudit.RadicalRotationFixed

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.RadicalRotationFixed.rotation_root,
      ``ManuscriptAudit.RadicalRotationFixed.exists_scalar_of_fixed] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
