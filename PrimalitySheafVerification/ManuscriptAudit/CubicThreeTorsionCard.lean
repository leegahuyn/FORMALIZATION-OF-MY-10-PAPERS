import Lean.Util.CollectAxioms
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.Tactic.NormNum
import PrimalitySheafVerification.ManuscriptAudit.CubicThreeTorsion

/-! Exactly nine actual geometric three-torsion points on the good cubic y²=x³+A. -/

namespace ManuscriptAudit.CubicThreeTorsionCard

open Polynomial WeierstrassCurve FiniteFieldPointCount CubicThreeTorsion

noncomputable section

variable {K : Type*} [Field K]

/-- For the centered cubic, the coefficient assumptions already imply good reduction. -/
theorem shortCubic_discriminant_ne_zero {A : K} (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (hA : A ≠ 0) : (shortCubic (0 : K) A).Δ ≠ 0 := by
  have hΔ : (shortCubic (0 : K) A).Δ = -((2 : K) ^ 4 * (3 : K) ^ 3 * A ^ 2) := by
    simp only [shortCubic, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  rw [hΔ]
  exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (pow_ne_zero _ h₂) (pow_ne_zero _ h₃))
    (pow_ne_zero _ hA))

variable [IsAlgClosed K] [DecidableEq K]

private abbrev PowerRoots (n : ℕ) (b : K) := {x : K // x ^ n = b}

private def powerPolynomial (n : ℕ) (b : K) : K[X] := X ^ n - C b

private theorem powerPolynomial_ne (n : ℕ) (b : K) (hn : 0 < n) :
    powerPolynomial n b ≠ 0 := by
  intro h
  have hd : (powerPolynomial n b).natDegree = n := natDegree_X_pow_sub_C
  rw [h, natDegree_zero] at hd
  omega

private def powerRootsEquiv (n : ℕ) (b : K) (hn : 0 < n) :
    PowerRoots n b ≃ ↥((powerPolynomial n b).rootSet K) where
  toFun x := ⟨x, (mem_rootSet_of_ne (powerPolynomial_ne n b hn)).mpr
    (by simpa [powerPolynomial, sub_eq_zero] using x.property)⟩
  invFun y := ⟨y, by simpa [powerPolynomial, sub_eq_zero] using
    (mem_rootSet_of_ne (powerPolynomial_ne n b hn)).mp y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem powerRoots_card (n : ℕ) (b : K) (hn : 0 < n)
    (hnK : (n : K) ≠ 0) (hb : b ≠ 0) : Nat.card (PowerRoots n b) = n := by
  have hs : (powerPolynomial n b).Separable := separable_X_pow_sub_C b hnK hb
  have hc := Polynomial.card_rootSet_eq_natDegree (K := K) hs (IsAlgClosed.splits _)
  rw [Nat.card_congr (powerRootsEquiv n b hn), Nat.card_eq_fintype_card, hc]
  exact natDegree_X_pow_sub_C

private theorem flexConstant_ne_zero {A : K} (h₂ : (2 : K) ≠ 0) (hA : A ≠ 0) :
    -(4 * A) ≠ 0 := by
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 ^ 2 by ring]
    exact pow_ne_zero _ h₂
  exact neg_ne_zero.mpr (mul_ne_zero h4 hA)

private def flexAbscissasEquiv {A : K} (hb : -(4 * A) ≠ 0) :
    FlexAbscissas A ≃ Option (PowerRoots 3 (-(4 * A))) where
  toFun x :=
    if hx : x.val = 0 then none else
      some ⟨x.val, by
        have h := (mul_eq_zero.mp x.property).resolve_left hx
        calc
          x.val ^ 3 = (x.val ^ 3 + 4 * A) - 4 * A := by ring
          _ = -(4 * A) := by rw [h, zero_sub]⟩
  invFun
    | none => ⟨0, zero_mul _⟩
    | some x => ⟨x.val, by rw [x.property, neg_add_cancel, mul_zero]⟩
  left_inv := by
    intro x
    by_cases hx : x.val = 0
    · simp only [dif_pos hx]
      exact Subtype.ext hx.symm
    · simp only [dif_neg hx]
  right_inv := by
    rintro (_ | x)
    · simp
    · have hx : x.val ≠ 0 := by
        intro h0
        exact hb (by simpa [h0] using x.property.symm)
      simp only [dif_neg hx]

theorem flexAbscissas_card {A : K} (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (hA : A ≠ 0) : Nat.card (FlexAbscissas A) = 4 := by
  let b := -(4 * A)
  letI : Fintype (PowerRoots 3 b) := Fintype.ofEquiv _ (powerRootsEquiv 3 b (by decide)).symm
  rw [Nat.card_congr (flexAbscissasEquiv (flexConstant_ne_zero h₂ hA)), Nat.card_eq_fintype_card,
    Fintype.card_option, ← Nat.card_eq_fintype_card]
  rw [powerRoots_card 3 b (by decide) (by simpa only [Nat.cast_ofNat] using h₃)
    (flexConstant_ne_zero h₂ hA)]

private theorem optionFlexCoordinates_card {A : K} (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (hA : A ≠ 0) : Nat.card (Option (FlexCoordinates A)) = 9 := by
  let b := -(4 * A)
  letI : Fintype (PowerRoots 3 b) := Fintype.ofEquiv _ (powerRootsEquiv 3 b (by decide)).symm
  letI : Fintype (FlexAbscissas A) :=
    Fintype.ofEquiv _ (flexAbscissasEquiv (flexConstant_ne_zero h₂ hA)).symm
  letI : ∀ x : FlexAbscissas A, Fintype (Ordinates A x) := fun x =>
    Fintype.ofEquiv _ (powerRootsEquiv 2 (x.val ^ 3 + A) (by decide)).symm
  have hx : Fintype.card (FlexAbscissas A) = 4 := by
    rw [← Nat.card_eq_fintype_card, flexAbscissas_card h₂ h₃ hA]
  have hy (x : FlexAbscissas A) : Fintype.card (Ordinates A x) = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact powerRoots_card 2 (x.val ^ 3 + A) (by decide)
      (by simpa only [Nat.cast_ofNat] using h₂) (ordinate_square_ne_zero h₃ hA x)
  norm_num [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_sigma,
    hy, hx, Finset.sum_const, nsmul_eq_mul]

theorem affineThreeTorsion_card {A : K} (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (hA : A ≠ 0) (hΔ : (shortCubic (0 : K) A).Δ ≠ 0) : Nat.card (ThreeTorsion A) = 9 :=
  (Nat.card_congr (affineThreeTorsionEquiv h₂ h₃ hA hΔ)).trans (optionFlexCoordinates_card h₂ h₃ hA)

theorem projectiveThreeTorsion_card {A : K} (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (hA : A ≠ 0) (hΔ : (shortCubic (0 : K) A).Δ ≠ 0) :
    Nat.card {P : (shortCubic (0 : K) A).toProjective.Point // 3 • P = 0} = 9 :=
  (Nat.card_congr (projectiveThreeTorsionEquiv h₂ h₃ hA hΔ)).trans (optionFlexCoordinates_card h₂ h₃ hA)

/-- The actual projective three-torsion of the centered cubic has nine points. -/
theorem projectiveThreeTorsion_card_of_coefficients {A : K} (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (hA : A ≠ 0) :
    Nat.card {P : (shortCubic (0 : K) A).toProjective.Point // 3 • P = 0} = 9 :=
  projectiveThreeTorsion_card h₂ h₃ hA (shortCubic_discriminant_ne_zero h₂ h₃ hA)

end
end ManuscriptAudit.CubicThreeTorsionCard

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicThreeTorsionCard.shortCubic_discriminant_ne_zero,
      ``ManuscriptAudit.CubicThreeTorsionCard.flexAbscissas_card,
      ``ManuscriptAudit.CubicThreeTorsionCard.affineThreeTorsion_card,
      ``ManuscriptAudit.CubicThreeTorsionCard.projectiveThreeTorsion_card,
      ``ManuscriptAudit.CubicThreeTorsionCard.projectiveThreeTorsion_card_of_coefficients] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
