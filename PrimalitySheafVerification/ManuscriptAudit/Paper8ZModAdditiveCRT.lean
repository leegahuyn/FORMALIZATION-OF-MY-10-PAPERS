import Lean.Util.CollectAxioms
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Tactic.LinearCombination

/-! Chinese-remainder factorization of the exact additive phase and weighted unit sum. -/

namespace ManuscriptAudit.Paper8ZModAdditiveCRT

open Finset

noncomputable section

theorem stdAddChar_chineseRemainder {n m : ℕ} [NeZero n] [NeZero m] (h : n.Coprime m)
    (u v : ℤ) (huv : u * (m : ℤ) + v * (n : ℤ) = 1) (z : ZMod (n * m)) :
    ZMod.stdAddChar z =
      ZMod.stdAddChar ((u : ZMod n) * (ZMod.chineseRemainder h z).1) *
      ZMod.stdAddChar ((v : ZMod m) * (ZMod.chineseRemainder h z).2) := by
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective z
  rw [map_intCast]
  change ZMod.stdAddChar (a : ZMod (n * m)) =
    ZMod.stdAddChar ((u : ZMod n) * (a : ZMod n)) * ZMod.stdAddChar ((v : ZMod m) * (a : ZMod m))
  rw [← Int.cast_mul, ← Int.cast_mul, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe,
    ← Complex.exp_add]
  congr 1
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
  have hZ := congrArg (fun a : ℤ => (a : ℂ)) huv
  push_cast at hZ ⊢
  field_simp [hn, hm]
  linear_combination -(2 * (Real.pi : ℂ) * Complex.I * (a : ℂ)) * hZ

def twistedSymmetricUnitSum {n : ℕ} [NeZero n] (χ : (ZMod n)ˣ → ℂ) (a : ZMod n) : ℂ :=
  ∑ x : (ZMod n)ˣ, χ x * ZMod.stdAddChar (a * ((x : ZMod n) + ((x⁻¹ : (ZMod n)ˣ) : ZMod n)))

def unitsChineseRemainder {n m : ℕ} (h : n.Coprime m) :
    (ZMod (n * m))ˣ ≃* (ZMod n)ˣ × (ZMod m)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans MulEquiv.prodUnits

theorem twistedSymmetricUnitSum_chineseRemainder {n m : ℕ} [NeZero n] [NeZero m] (h : n.Coprime m)
    (u v a : ℤ) (huv : u * (m : ℤ) + v * (n : ℤ) = 1)
    (χ : (ZMod n)ˣ → ℂ) (ρ : (ZMod m)ˣ → ℂ) :
    twistedSymmetricUnitSum (fun x => χ (unitsChineseRemainder h x).1 * ρ (unitsChineseRemainder h x).2)
      (a : ZMod (n * m)) =
      twistedSymmetricUnitSum χ ((u * a : ℤ) : ZMod n) *
      twistedSymmetricUnitSum ρ ((v * a : ℤ) : ZMod m) := by
  let e := unitsChineseRemainder h
  let F (x : (ZMod n)ˣ) := χ x *
    ZMod.stdAddChar (((u * a : ℤ) : ZMod n) * ((x : ZMod n) + ((x⁻¹ : (ZMod n)ˣ) : ZMod n)))
  let G (y : (ZMod m)ˣ) := ρ y *
    ZMod.stdAddChar (((v * a : ℤ) : ZMod m) * ((y : ZMod m) + ((y⁻¹ : (ZMod m)ˣ) : ZMod m)))
  have hC (x : (ZMod (n * m))ˣ) :
      (ZMod.chineseRemainder h (x : ZMod (n * m))) =
        (((e x).1 : ZMod n), ((e x).2 : ZMod m)) := rfl
  have hI (x : (ZMod (n * m))ˣ) :
      (ZMod.chineseRemainder h ((x⁻¹ : (ZMod (n * m))ˣ) : ZMod (n * m))) =
        ((((e x).1⁻¹ : (ZMod n)ˣ) : ZMod n), (((e x).2⁻¹ : (ZMod m)ˣ) : ZMod m)) := by
    rw [hC, map_inv] <;> rfl
  let L (x : (ZMod (n * m))ˣ) :=
    (χ (e x).1 * ρ (e x).2) *
      ZMod.stdAddChar ((a : ZMod (n * m)) * ((x : ZMod (n * m)) + ((x⁻¹ : (ZMod (n * m))ˣ) : ZMod (n * m))))
  have hTerm (x : (ZMod (n * m))ˣ) : L x = F (e x).1 * G (e x).2 := by
    unfold L F G
    rw [stdAddChar_chineseRemainder h u v huv, map_mul, map_add, map_intCast, hC, hI]
    change _ * (ZMod.stdAddChar ((u : ZMod n) * ((a : ZMod n) *
        (((e x).1 : ZMod n) + (((e x).1⁻¹ : (ZMod n)ˣ) : ZMod n)))) *
      ZMod.stdAddChar ((v : ZMod m) * ((a : ZMod m) *
        (((e x).2 : ZMod m) + (((e x).2⁻¹ : (ZMod m)ˣ) : ZMod m))))) = _
    rw [← mul_assoc (u : ZMod n), ← mul_assoc (v : ZMod m), ← Int.cast_mul, ← Int.cast_mul]
    ring
  calc
    _ = ∑ z : (ZMod n)ˣ × (ZMod m)ˣ, F z.1 * G z.2 :=
      Fintype.sum_equiv e.toEquiv L (fun z => F z.1 * G z.2) hTerm
    _ = _ := by
      change _ = (∑ x : (ZMod n)ˣ, F x) * (∑ y : (ZMod m)ˣ, G y)
      rw [Fintype.sum_prod_type, Finset.sum_mul]
      simp_rw [Finset.mul_sum]

end
end ManuscriptAudit.Paper8ZModAdditiveCRT

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8ZModAdditiveCRT.stdAddChar_chineseRemainder,
      ``ManuscriptAudit.Paper8ZModAdditiveCRT.twistedSymmetricUnitSum_chineseRemainder] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
