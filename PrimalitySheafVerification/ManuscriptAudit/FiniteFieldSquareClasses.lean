import Lean.Util.CollectAxioms
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.LinearCombination
import PrimalitySheafVerification.ManuscriptAudit.KummerPIDUnitQuotient

/-! The two square classes in a finite field of odd characteristic. -/

namespace ManuscriptAudit.FiniteFieldSquareClasses

open KummerPIDUnitQuotient

noncomputable section

variable (K : Type) [Field K]

private def squareHom : Additive Kˣ →+ Additive Kˣ where
  toFun u := Additive.ofMul (u.toMul ^ (2 : ℕ))
  map_zero' := by
    change Additive.ofMul ((1 : Kˣ) ^ (2 : ℕ)) = 0
    simp
  map_add' := by
    intro u v
    apply Additive.ext
    change (u.toMul * v.toMul) ^ (2 : ℕ) = u.toMul ^ (2 : ℕ) * v.toMul ^ (2 : ℕ)
    exact mul_pow _ _ _

private def negativeUnit : Kˣ := Units.mk0 (-1 : K) (neg_ne_zero.mpr one_ne_zero)

private def kernelLabel (b : Bool) : (squareHom K).ker :=
  match b with
  | false => ⟨0, by exact (squareHom K).map_zero⟩
  | true => ⟨Additive.ofMul (negativeUnit K), by
      apply Additive.ext
      apply Units.ext
      change ((negativeUnit K ^ (2 : ℕ) : Kˣ) : K) = 1
      simp [negativeUnit]⟩

theorem squareRootUnit_card (h₂ : (2 : K) ≠ 0) :
    Nat.card (squareHom K).ker = 2 := by
  have hNeg : (-1 : K) ≠ 1 := by
    intro h
    apply h₂
    calc
      (2 : K) = 1 + 1 := by norm_num
      _ = 1 + (-1) := by rw [h]
      _ = 0 := add_neg_cancel 1
  have hinj : Function.Injective (kernelLabel K) := by
    intro a b h
    cases a <;> cases b
    · rfl
    · exfalso
      exact hNeg (congrArg (fun u : (squareHom K).ker => (u.1.toMul : K)) h.symm)
    · exfalso
      exact hNeg (congrArg (fun u : (squareHom K).ker => (u.1.toMul : K)) h)
    · rfl
  have hsurj : Function.Surjective (kernelLabel K) := by
    intro u
    have hu : squareHom K u.1 = 0 := u.2
    have hSq : (u.1.toMul : K) ^ (2 : ℕ) = 1 := by
      simpa [squareHom] using congrArg (fun t : Additive Kˣ => (t.toMul : K)) hu
    have hProd : ((u.1.toMul : K) - 1) * ((u.1.toMul : K) + 1) = 0 := by
      linear_combination hSq
    rcases mul_eq_zero.mp hProd with h | h
    · refine ⟨false, Subtype.ext (Additive.ext (Units.ext ?_))⟩
      exact (sub_eq_zero.mp h).symm
    · refine ⟨true, Subtype.ext (Additive.ext (Units.ext ?_))⟩
      change (-1 : K) = (u.1.toMul : K)
      linear_combination -h
  simpa using (Nat.card_congr (Equiv.ofBijective (kernelLabel K) ⟨hinj, hsurj⟩)).symm

private theorem range_squareHom_eq : (squareHom K).range = powerSubgroup K 2 := by
  ext x
  rw [AddMonoidHom.mem_range, mem_powerSubgroup]
  constructor
  · rintro ⟨u, h⟩
    refine ⟨u.toMul, ?_⟩
    change Additive.ofMul (u.toMul ^ (2 : ℕ)) = x at h
    exact congrArg Additive.toMul h
  · rintro ⟨u, h⟩
    refine ⟨Additive.ofMul u, ?_⟩
    change Additive.ofMul (u ^ (2 : ℕ)) = x
    exact congrArg Additive.ofMul h

theorem squareClass_card [Finite K] (h₂ : (2 : K) ≠ 0) :
    Nat.card (Additive Kˣ ⧸ powerSubgroup K 2) = 2 := by
  let f := squareHom K
  have hKer : Nat.card f.ker = 2 := squareRootUnit_card K h₂
  have hRange : f.ker.index = Nat.card f.range :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv
  have h₁ := f.ker.index_mul_card
  rw [hRange, hKer] at h₁
  have h₂' := f.range.card_mul_index
  have hIndex : f.range.index = 2 := by
    apply mul_left_cancel₀ (Nat.card_pos (α := f.range)).ne'
    exact h₂'.trans h₁.symm
  change Nat.card (Additive Kˣ ⧸ powerSubgroup K 2) = _
  rw [← range_squareHom_eq]
  exact hIndex

theorem exists_nonsquare_unit [Finite K] (h₂ : (2 : K) ≠ 0) :
    ∃ u : Kˣ, ¬ ∃ v : Kˣ, v ^ (2 : ℕ) = u := by
  let Q := Additive Kˣ ⧸ powerSubgroup K 2
  have hQ : Nat.card Q = 2 := squareClass_card K h₂
  letI : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQ]; decide)
  letI : Nontrivial Q := Finite.one_lt_card_iff_nontrivial.mp (by rw [hQ]; decide)
  obtain ⟨c, hc⟩ := exists_ne (0 : Q)
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective c
  exact ⟨x.toMul, fun hx => hc ((QuotientAddGroup.eq_zero_iff x).mpr
    ((mem_powerSubgroup 2 x).mpr hx))⟩

end
end ManuscriptAudit.FiniteFieldSquareClasses

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.FiniteFieldSquareClasses.squareRootUnit_card,
      ``ManuscriptAudit.FiniteFieldSquareClasses.squareClass_card,
      ``ManuscriptAudit.FiniteFieldSquareClasses.exists_nonsquare_unit] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
