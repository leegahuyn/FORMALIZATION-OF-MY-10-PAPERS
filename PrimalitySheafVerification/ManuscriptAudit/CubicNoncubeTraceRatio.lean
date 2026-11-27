import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.CubicFiniteFieldProduct
import PrimalitySheafVerification.ManuscriptAudit.CubicNoRootTraceModFour

/-! The exact arithmetic trace residue of a noncube sextic twist. -/

namespace ManuscriptAudit.CubicNoncubeTraceRatio

open FiniteFieldPointCount CubicFiniteFieldProduct CubicNoRootTraceModFour

noncomputable section

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- The field sextic ratio records both the geometric root cycle and the quadratic
sign controlling the signed point trace modulo four. -/
theorem noncube_ratio_trace (L : Type*) [Field L] [Algebra K L] [IsAlgClosed L]
    {A z : K} (hA : A ≠ 0) (hz : IsPrimitiveRoot z 3) (hNc : ¬ ∃ x : K, x ^ 3 = A)
    (hchar : ringChar K ≠ 2) (hΔ : (shortCubic (0 : K) A).Δ ≠ 0)
    (hq₄ : (Fintype.card K : ZMod 4) = 3) {k : ℕ}
    (hq : Fintype.card K = 6 * k + 1) :
    let v := A ^ k
    (v ^ 2) ^ 3 = 1 ∧ v ^ 2 ≠ 1 ∧
      v ^ 3 = (quadraticChar K A : K) ∧
      (((Fintype.card K : ℤ) + 1 -
        (Nat.card (shortCubic (0 : K) A).toProjective.Point : ℤ) : ℤ) : ZMod 4) =
        ((quadraticChar K A : ℤ) : ZMod 4) * (quadraticChar K (v ^ 2 - 1) : ZMod 4) := by
  let v := A ^ k
  let i := algebraMap K L
  have hNo (x : K) : x ^ 3 + A ≠ 0 := by
    intro hx
    exact hNc ⟨-x, by linear_combination -hx⟩
  have hv : v ^ 6 = 1 := by
    have hn : Fintype.card K - 1 = k * 6 := by omega
    dsimp only [v]
    rw [← pow_mul, ← hn]
    exact FiniteField.pow_card_sub_one_eq_one A hA
  have hCycleCube : (v ^ 2) ^ 3 = 1 := by
    rw [← pow_mul]
    exact hv
  have hv₃ : v ^ 3 = (quadraticChar K A : K) := by
    have hn : k * 3 = Fintype.card K / 2 := by omega
    dsimp only [v]
    rw [← pow_mul, hn]
    exact (quadraticChar_eq_pow_of_char_ne_two' hchar A).symm
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (i A) (by decide : 0 < (6 : ℕ))
  let t := -(u ^ 2)
  have ht : t ^ 3 = -i A := by
    calc
      _ = -(u ^ 6) := by dsimp only [t]; ring
      _ = _ := by rw [hu]
  have hUq : u ^ Fintype.card K = u * i v := by
    rw [hq, pow_succ, pow_mul, hu, ← map_pow, mul_comm]
  have hCycle : t ^ Fintype.card K = i (v ^ 2) * t := by
    let g := FiniteField.frobeniusAlgHom K L
    change g t = i (v ^ 2) * t
    dsimp only [t]
    rw [map_neg, map_pow, show g u = u * i v from hUq, map_pow]
    ring
  have hc₀ : v ^ 2 ≠ 1 := by
    intro he
    have hf : t ^ Fintype.card K = t := by rw [hCycle, he, map_one, one_mul]
    obtain ⟨x, hx⟩ := (WeierstrassFiniteFieldFixedCount.pow_card_eq_self_iff K L t).mp hf
    apply hNo x
    apply i.injective
    rw [map_add, map_pow, map_zero, hx, ht, neg_add_cancel]
  refine ⟨hCycleCube, hc₀, hv₃, ?_⟩
  have hcχ : quadraticChar K (v ^ 2 - 1) ^ 3 = quadraticChar K (v ^ 2 - 1) := by
    rcases quadraticChar_dichotomy (sub_ne_zero.mpr hc₀) with h | h <;> norm_num [h]
  rw [signed_trace_eq_quadratic_product hchar hΔ hq₄ hNo,
    product_cubic_of_frobenius_ratio K L hchar hz ht hCycle, map_mul, map_pow, hcχ, Int.cast_mul]

end
end ManuscriptAudit.CubicNoncubeTraceRatio

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicNoncubeTraceRatio.noncube_ratio_trace
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
