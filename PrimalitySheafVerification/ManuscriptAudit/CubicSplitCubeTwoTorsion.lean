import Lean.Util.CollectAxioms
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.CubicThreeTorsionOrdinate

/-! The four rational two-torsion points of a split centered cubic with cube coefficient. -/

namespace ManuscriptAudit.CubicSplitCubeTwoTorsion

open FiniteFieldPointCount CubicTwoTorsion CubicThreeTorsionOrdinate
open CubicThreeTorsionCard TorsionFrobeniusModule

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K]

private def rootsEquiv {A z t : K} (hA : A ≠ 0) (hz : IsPrimitiveRoot z 3)
    (ht : t ^ 3 = -A) : Fin 3 ≃ CubicRoots (0 : K) A := by
  have ht₀ : t ≠ 0 := by
    intro he
    rw [he, zero_pow (by decide)] at ht
    exact hA (neg_eq_zero.mp ht.symm)
  let e (i : Fin 3) : CubicRoots (0 : K) A := ⟨t * z ^ i.val, by
    have hp : (z ^ i.val) ^ 3 = 1 := by
      rw [← pow_mul, Nat.mul_comm i.val 3, pow_mul, hz.pow_eq_one, one_pow]
    change (t * z ^ i.val) ^ 3 - 0 * (t * z ^ i.val) + A = 0
    rw [zero_mul, sub_zero, mul_pow, ht, hp, mul_one, neg_add_cancel]⟩
  refine Equiv.ofBijective e ⟨?_, ?_⟩
  · intro i j h
    apply Fin.ext
    apply hz.pow_inj i.isLt j.isLt
    exact mul_left_cancel₀ ht₀ (congrArg (fun x : CubicRoots (0 : K) A => x.val) h)
  · intro x
    have hx : x.val ^ 3 = -A := by
      have he := x.property
      change x.val ^ 3 - 0 * x.val + A = 0 at he
      simp only [zero_mul, sub_zero] at he
      exact eq_neg_of_add_eq_zero_left he
    have hdiv : (x.val / t) ^ 3 = 1 := by
      rw [div_pow, hx, ht, div_self (neg_ne_zero.mpr hA)]
    obtain ⟨j, hj, he⟩ := hz.eq_pow_of_pow_eq_one hdiv
    refine ⟨⟨j, hj⟩, Subtype.ext ?_⟩
    change t * z ^ j = x.val
    rw [he, mul_comm, div_mul_cancel₀ _ ht₀]

/-- Over a field containing a primitive cube root, a nonzero cube coefficient gives
all four native two-torsion points over the base field. -/
theorem rationalTwoTorsion_card {A z : K}
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0)
    (hz : IsPrimitiveRoot z 3) (hc : ∃ u : K, u ^ 3 = A) :
    Nat.card (Torsion 2 (Curve A).Point) = 4 := by
  obtain ⟨u, hu⟩ := hc
  have ht : (-u) ^ 3 = -A := by
    rw [← hu]
    ring
  let e := (carrierEquiv 2 (Curve A).Point).trans
    ((affineTwoTorsionEquiv (shortCubic_discriminant_ne_zero h₂ h₃ hA) h₂).trans
      (rootsEquiv hA hz ht).symm.optionCongr)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_fin]

end
end ManuscriptAudit.CubicSplitCubeTwoTorsion

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicSplitCubeTwoTorsion.rationalTwoTorsion_card
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
