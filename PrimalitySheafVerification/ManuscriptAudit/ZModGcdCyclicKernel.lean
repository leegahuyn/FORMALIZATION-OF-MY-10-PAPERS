import Lean.Util.CollectAxioms
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import PrimalitySheafVerification.ManuscriptAudit.IntegerGcdCyclicKernel

/-! The kernel of multiplication on native residues is a cyclic group
of precisely the gcd order. -/

namespace ManuscriptAudit.ZModGcdCyclicKernel

open IntegerGcdCyclicKernel

variable (m n : ℕ)

private abbrev K :=
  LinearMap.ker ((n : ℤ) • (LinearMap.id : ZMod m →ₗ[ℤ] ZMod m))

private abbrev cofactor : ℤ := (m / Nat.gcd m n : ℕ)

/-- The integer multiple of the cofactor lies in the true scalar kernel. -/
private def representative (hm : 0 < m) : ℤ →+ K m n where
  toFun a := ⟨((cofactor m n * a : ℤ) : ZMod m), by
    change (n : ℤ) • (((cofactor m n * a : ℤ) : ZMod m)) = 0
    rw [zsmul_eq_mul, ← Int.cast_mul, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact (cofactor_dvd_iff (n := n) hm (cofactor m n * a)).mp ⟨a, rfl⟩⟩
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by
    change (((cofactor m n * (a + b) : ℤ) : ZMod m)) =
      ((cofactor m n * a : ℤ) : ZMod m) + ((cofactor m n * b : ℤ) : ZMod m)
    rw [mul_add, Int.cast_add])

private theorem representative_eq_zero (hm : 0 < m) (a : ℤ) :
    representative m n hm a = 0 ↔ (Nat.gcd m n : ℤ) ∣ a := by
  rw [gcd_dvd_iff_cofactor_mul hm]
  constructor
  · intro h
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mp
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext ((ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mpr h)

/-- The explicit cofactor map from gcd residues to the native kernel. -/
def cofactorMap (hm : 0 < m) : ZMod (Nat.gcd m n) →+ K m n :=
  ZMod.lift (Nat.gcd m n) ⟨representative m n hm,
    (representative_eq_zero m n hm _).mpr dvd_rfl⟩

@[simp] theorem cofactorMap_intCast (hm : 0 < m) (a : ℤ) :
    (cofactorMap m n hm (a : ZMod (Nat.gcd m n)) : ZMod m) =
      ((cofactor m n * a : ℤ) : ZMod m) := by
  unfold cofactorMap
  rw [ZMod.lift_coe]
  rfl

theorem cofactorMap_bijective (hm : 0 < m) :
    Function.Bijective (cofactorMap m n hm) := by
  constructor
  · intro x y hxy
    apply sub_eq_zero.mp
    have hZero : cofactorMap m n hm (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    obtain ⟨a, ha⟩ := ZMod.intCast_surjective (n := Nat.gcd m n) (x - y)
    rw [← ha] at hZero ⊢
    unfold cofactorMap at hZero
    rw [ZMod.lift_coe] at hZero
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
      ((representative_eq_zero m n hm a).mp hZero)
  · intro x
    obtain ⟨a, ha⟩ := ZMod.intCast_surjective x.val
    have h : (n : ℤ) • x.val = 0 := x.property
    rw [← ha, zsmul_eq_mul, ← Int.cast_mul,
      ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    obtain ⟨q, hq⟩ := (cofactor_dvd_iff (n := n) hm a).mpr h
    refine ⟨(q : ZMod (Nat.gcd m n)), Subtype.ext ?_⟩
    rw [cofactorMap_intCast, ← hq, ha]

/-- The kernel calculation preserves its genuine integral module structure. -/
noncomputable def gcdResiduesEquivKernel (hm : 0 < m) :
    ZMod (Nat.gcd m n) ≃ₗ[ℤ] K m n := by
  let e := AddEquiv.ofBijective (cofactorMap m n hm) (cofactorMap_bijective m n hm)
  exact e.toIntLinearEquiv

end ManuscriptAudit.ZModGcdCyclicKernel

open Lean Elab Command in
run_cmd do
  let names := [``ManuscriptAudit.ZModGcdCyclicKernel.cofactorMap_bijective,
    ``ManuscriptAudit.ZModGcdCyclicKernel.gcdResiduesEquivKernel]
  for name in names do
    let ax ← collectAxioms name
    let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
