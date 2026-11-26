import Lean.Util.CollectAxioms
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.Tactic.NormNum
import PrimalitySheafVerification.ManuscriptAudit.CubicTwoTorsion

/-! The geometric two-torsion count for every nonsingular short Weierstrass cubic. -/

namespace ManuscriptAudit.CubicGeneralTwoTorsionCard

open Polynomial CubicTwoTorsion FiniteFieldPointCount

noncomputable section

variable {K : Type*} [Field K]

private def cubicPolynomial (c A : K) : K[X] := X ^ 3 - C c * X + C A

private theorem cubicPolynomial_degree (c A : K) : (cubicPolynomial c A).natDegree = 3 := by
  have hmul : (C c * (X : K[X])).natDegree ≤ 1 := by
    simpa using natDegree_C_mul_le c (X : K[X])
  have htail : (-(C c * (X : K[X])) + C A).natDegree ≤ 1 := by
    simpa only [natDegree_add_C, natDegree_neg] using hmul
  have hdegree : (-(C c * (X : K[X])) + C A).natDegree < ((X : K[X]) ^ 3).natDegree := by
    rw [natDegree_X_pow]
    omega
  rw [cubicPolynomial, sub_eq_add_neg, add_assoc, natDegree_add_eq_left_of_natDegree_lt hdegree,
    natDegree_X_pow]

private theorem cubicPolynomial_ne (c A : K) : cubicPolynomial c A ≠ 0 := by
  intro h
  have hd := cubicPolynomial_degree c A
  rw [h, natDegree_zero] at hd
  omega

private theorem aeval_cubicPolynomial_derivative (c A x : K) :
    aeval x (derivative (cubicPolynomial c A)) = 3 * x ^ 2 - c := by
  norm_num [cubicPolynomial, derivative_X_pow, derivative_C_mul_X]

variable [IsAlgClosed K]

theorem cubicPolynomial_separable {c A : K} (hΔ : (shortCubic c A).Δ ≠ 0) :
    (cubicPolynomial c A).Separable := by
  rw [separable_def]
  refine (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed K K
    (cubicPolynomial c A) (derivative (cubicPolynomial c A))).mpr ?_
  intro x
  by_cases hx : x ^ 3 - c * x + A = 0
  · right
    have hn : (CubicAffine c A).Nonsingular x 0 := by
      rw [← WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ,
        WeierstrassCurve.Affine.equation_iff]
      simpa [CubicAffine, shortCubic, sub_eq_add_neg, neg_mul] using hx.symm
    have hp := ((CubicAffine c A).nonsingular_iff x 0).mp hn
    have hd : (0 : K) ≠ 3 * x ^ 2 - c := by
      simpa [CubicAffine, shortCubic, sub_eq_add_neg] using hp.2
    rw [aeval_cubicPolynomial_derivative]
    exact hd.symm
  · left
    simpa [cubicPolynomial] using hx

variable [DecidableEq K]

private def cubicRootSetEquiv (c A : K) :
    CubicRoots c A ≃ ↥((cubicPolynomial c A).rootSet K) where
  toFun x := ⟨x, (mem_rootSet_of_ne (cubicPolynomial_ne c A)).mpr
    (by simpa [cubicPolynomial] using x.property)⟩
  invFun y := ⟨y, by simpa [cubicPolynomial] using
    (mem_rootSet_of_ne (cubicPolynomial_ne c A)).mp y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem cubicRoots_card {c A : K} (hΔ : (shortCubic c A).Δ ≠ 0) :
    Nat.card (CubicRoots c A) = 3 := by
  classical
  have hc :=
    Polynomial.card_rootSet_eq_natDegree (K := K) (cubicPolynomial_separable hΔ) (IsAlgClosed.splits _)
  rw [Nat.card_congr (cubicRootSetEquiv c A), Nat.card_eq_fintype_card, hc, cubicPolynomial_degree]

private theorem optionCubicRoots_card {c A : K} (hΔ : (shortCubic c A).Δ ≠ 0) :
    Nat.card (Option (CubicRoots c A)) = 4 := by
  classical
  letI : Fintype (CubicRoots c A) := Fintype.ofEquiv _ (cubicRootSetEquiv c A).symm
  rw [Nat.card_eq_fintype_card, Fintype.card_option, ← Nat.card_eq_fintype_card, cubicRoots_card hΔ]

theorem affineTwoTorsion_card {c A : K} (h2 : (2 : K) ≠ 0)
    (hΔ : (shortCubic c A).Δ ≠ 0) :
    Nat.card (TwoTorsion c A) = 4 :=
  (Nat.card_congr (affineTwoTorsionEquiv hΔ h2)).trans (optionCubicRoots_card hΔ)

theorem projectiveTwoTorsion_card {c A : K} (h2 : (2 : K) ≠ 0)
    (hΔ : (shortCubic c A).Δ ≠ 0) :
    Nat.card {P : (shortCubic c A).toProjective.Point // 2 • P = 0} = 4 :=
  (Nat.card_congr (projectiveTwoTorsionEquiv hΔ h2)).trans (optionCubicRoots_card hΔ)

end
end ManuscriptAudit.CubicGeneralTwoTorsionCard

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicGeneralTwoTorsionCard.cubicPolynomial_separable,
      ``ManuscriptAudit.CubicGeneralTwoTorsionCard.cubicRoots_card,
      ``ManuscriptAudit.CubicGeneralTwoTorsionCard.affineTwoTorsion_card,
      ``ManuscriptAudit.CubicGeneralTwoTorsionCard.projectiveTwoTorsion_card] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
