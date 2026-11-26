import Lean.Util.CollectAxioms
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Separable
import PrimalitySheafVerification.ManuscriptAudit.CubicTwoTorsion

/-! There are exactly four actual geometric two-torsion points in the good cubic family. -/

namespace ManuscriptAudit.CubicTwoTorsionCard

open Polynomial CubicTwoTorsion FiniteFieldPointCount

noncomputable section

variable {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]

private def cubicPolynomial (A : K) : K[X] := X ^ 3 - C (-A)

private theorem cubicPolynomial_degree (A : K) : (cubicPolynomial A).natDegree = 3 :=
  natDegree_X_pow_sub_C

private theorem cubicPolynomial_ne (A : K) : cubicPolynomial A ≠ 0 := by
  intro h
  have hd := cubicPolynomial_degree A
  rw [h, natDegree_zero] at hd
  omega

private def cubicRootSetEquiv (A : K) :
    CubicRoots (0 : K) A ≃ ↥((cubicPolynomial A).rootSet K) where
  toFun x := ⟨x, (mem_rootSet_of_ne (cubicPolynomial_ne A)).mpr
    (by simpa [cubicPolynomial] using x.property)⟩
  invFun y := ⟨y, by simpa [cubicPolynomial] using
    (mem_rootSet_of_ne (cubicPolynomial_ne A)).mp y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem cubicRoots_card {A : K} (h3 : (3 : K) ≠ 0) (hA : A ≠ 0) :
    Nat.card (CubicRoots (0 : K) A) = 3 := by
  classical
  have hs : (cubicPolynomial A).Separable :=
    separable_X_pow_sub_C (-A) h3 (neg_ne_zero.mpr hA)
  have hc := Polynomial.card_rootSet_eq_natDegree (K := K) hs (IsAlgClosed.splits _)
  rw [Nat.card_congr (cubicRootSetEquiv A), Nat.card_eq_fintype_card, hc, cubicPolynomial_degree]

private theorem optionCubicRoots_card {A : K} (h3 : (3 : K) ≠ 0) (hA : A ≠ 0) :
    Nat.card (Option (CubicRoots (0 : K) A)) = 4 := by
  classical
  letI : Fintype (CubicRoots (0 : K) A) := Fintype.ofEquiv _ (cubicRootSetEquiv A).symm
  rw [Nat.card_eq_fintype_card, Fintype.card_option, ← Nat.card_eq_fintype_card,
    cubicRoots_card h3 hA]

theorem affineTwoTorsion_card {A : K} (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (hA : A ≠ 0) (hΔ : (shortCubic (0 : K) A).Δ ≠ 0) :
    Nat.card (TwoTorsion (0 : K) A) = 4 :=
  (Nat.card_congr (affineTwoTorsionEquiv hΔ h2)).trans (optionCubicRoots_card h3 hA)

theorem projectiveTwoTorsion_card {A : K} (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (hA : A ≠ 0) (hΔ : (shortCubic (0 : K) A).Δ ≠ 0) :
    Nat.card {P : (shortCubic (0 : K) A).toProjective.Point // 2 • P = 0} = 4 :=
  (Nat.card_congr (projectiveTwoTorsionEquiv hΔ h2)).trans (optionCubicRoots_card h3 hA)

end
end ManuscriptAudit.CubicTwoTorsionCard

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicTwoTorsionCard.cubicRoots_card,
      ``ManuscriptAudit.CubicTwoTorsionCard.affineTwoTorsion_card,
      ``ManuscriptAudit.CubicTwoTorsionCard.projectiveTwoTorsion_card] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
