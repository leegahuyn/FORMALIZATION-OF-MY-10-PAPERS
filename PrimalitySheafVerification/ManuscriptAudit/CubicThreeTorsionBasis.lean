import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.CubicThreeTorsionOrdinate
import PrimalitySheafVerification.ManuscriptAudit.TorsionFrobeniusModule

/-! A native basis using one vertical and one nonvertical flex on the centered cubic. -/

namespace ManuscriptAudit.CubicThreeTorsionBasis

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsion CubicThreeTorsionCard
open CubicThreeTorsionOrdinate TorsionFrobeniusModule

noncomputable section

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

variable {K : Type*} [Field K] {A : K}

structure FlexPair (A : K) where
  x : K
  a : K
  b : K
  x_ne : x ≠ 0
  x_cube : x ^ 3 = -(4 * A)
  a_square : a ^ 2 = A
  b_square : b ^ 2 = -(3 * A)

theorem flexPair_nonempty [IsAlgClosed K] (h₂ : (2 : K) ≠ 0) (hA : A ≠ 0) :
    Nonempty (FlexPair A) := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (-(4 * A)) (n := 3) (by decide)
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq A (n := 2) (by decide)
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (-(3 * A)) (n := 2) (by decide)
  have h₄ : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 ^ 2 by ring]
    exact pow_ne_zero _ h₂
  have hx₀ : x ≠ 0 := by
    intro h
    exact neg_ne_zero.mpr (mul_ne_zero h₄ hA) (by simpa [h] using hx.symm)
  exact ⟨⟨x, a, b, hx₀, hx, ha, hb⟩⟩

variable [DecidableEq K]
variable (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0) (D : FlexPair A)

abbrev T₃ (A : K) := Torsion 3 (Curve A).Point

private theorem vertical_nonsingular : (Curve A).Nonsingular 0 D.a :=
  (nonsingular_iff (shortCubic_discriminant_ne_zero h₂ h₃ hA) _ _).mpr
    (by simpa using D.a_square)

private theorem horizontal_nonsingular : (Curve A).Nonsingular D.x D.b :=
  (nonsingular_iff (shortCubic_discriminant_ne_zero h₂ h₃ hA) _ _).mpr (by
    rw [D.b_square, D.x_cube]
    ring)

def vertical : T₃ A := by
  let h := vertical_nonsingular h₂ h₃ hA D
  refine ⟨.some 0 D.a h, (mem_iff 3 _ _).mpr ?_⟩
  apply (three_nsmul_affine_some_iff h₂ h₃ (shortCubic_discriminant_ne_zero h₂ h₃ hA) h).mpr
  refine ⟨?_, zero_mul _⟩
  intro ha
  exact hA (by simpa [ha] using D.a_square.symm)

def horizontal : T₃ A := by
  let h := horizontal_nonsingular h₂ h₃ hA D
  refine ⟨.some D.x D.b h, (mem_iff 3 _ _).mpr ?_⟩
  apply (three_nsmul_affine_some_iff h₂ h₃ (shortCubic_discriminant_ne_zero h₂ h₃ hA) h).mpr
  exact ⟨ordinate_nonzero_of_horizontal h₃ hA D.b_square, by rw [D.x_cube, neg_add_cancel, mul_zero]⟩

@[simp] theorem abscissa_vertical :
    abscissa (inclusion 3 _ (vertical h₂ h₃ hA D)) = 0 := rfl

@[simp] theorem ordinate_vertical :
    ordinate (inclusion 3 _ (vertical h₂ h₃ hA D)) = D.a := rfl

@[simp] theorem abscissa_horizontal :
    abscissa (inclusion 3 _ (horizontal h₂ h₃ hA D)) = D.x := rfl

@[simp] theorem ordinate_horizontal :
    ordinate (inclusion 3 _ (horizontal h₂ h₃ hA D)) = D.b := rfl

theorem scalar_cases : ∀ r : ZMod 3, r = 0 ∨ r = 1 ∨ r = -1 := by decide

theorem abscissa_smul_vertical (r : ZMod 3) :
    abscissa (inclusion 3 _ (r • vertical h₂ h₃ hA D)) = 0 := by
  rcases scalar_cases r with rfl | rfl | rfl <;> simp

theorem vertical_ne_zero : vertical h₂ h₃ hA D ≠ 0 := by
  intro h
  have ha := congrArg (fun P : T₃ A => ordinate (inclusion 3 _ P)) h
  have hzero : D.a = 0 := by simpa using ha
  exact hA (by simpa [hzero] using D.a_square.symm)

theorem ordinate_horizontal_add_vertical :
    ordinate (inclusion 3 _ (horizontal h₂ h₃ hA D + vertical h₂ h₃ hA D)) = D.b := by
  rw [map_add]
  exact ordinate_add_vertical D.x_ne D.x_cube D.a_square D.b_square _ _

theorem ordinate_horizontal_sub_vertical :
    ordinate (inclusion 3 _ (horizontal h₂ h₃ hA D - vertical h₂ h₃ hA D)) = D.b := by
  rw [map_sub]
  exact ordinate_sub_vertical D.x_ne D.x_cube D.a_square D.b_square _ _

/-- The first basis coefficient is detected by the ordinate off the invariant vertical line. -/
theorem ordinate_nonvertical_sum (r s : ZMod 3) (hr : r ≠ 0) :
    ordinate (inclusion 3 _ (r • horizontal h₂ h₃ hA D + s • vertical h₂ h₃ hA D)) =
      if r = 1 then D.b else -D.b := by
  let U := horizontal h₂ h₃ hA D
  let T := vertical h₂ h₃ hA D
  have ha : ordinate (inclusion 3 _ (U + T)) = D.b :=
    ordinate_horizontal_add_vertical h₂ h₃ hA D
  have hs : ordinate (inclusion 3 _ (U - T)) = D.b :=
    ordinate_horizontal_sub_vertical h₂ h₃ hA D
  have hn : (-1 : ZMod 3) ≠ 1 := by decide
  change ordinate (inclusion 3 _ (r • U + s • T)) = _
  rcases scalar_cases r with rfl | rfl | rfl
  · exact (hr rfl).elim
  · rw [one_smul, if_pos rfl]
    rcases scalar_cases s with rfl | rfl | rfl
    · simp [U]
    · simpa only [one_smul] using ha
    · simpa only [neg_one_smul, sub_eq_add_neg] using hs
  · rw [neg_one_smul, if_neg hn]
    rcases scalar_cases s with rfl | rfl | rfl
    · simp [U]
    · rw [one_smul, show -U + T = -(U - T) by abel, map_neg, ordinate_neg, hs]
    · rw [neg_one_smul, show -U + -T = -(U + T) by abel, map_neg, ordinate_neg, ha]

variable [IsAlgClosed K]

theorem card_torsion : Nat.card (T₃ A) = 9 :=
  (Nat.card_congr (carrierEquiv 3 _)).trans
    (affineThreeTorsion_card h₂ h₃ hA (shortCubic_discriminant_ne_zero h₂ h₃ hA))

theorem finite_torsion : Finite (T₃ A) :=
  Nat.finite_of_card_ne_zero (by rw [card_torsion h₂ h₃ hA]; decide)

theorem finrank_torsion : Module.finrank (ZMod 3) (T₃ A) = 2 := by
  letI := finite_torsion h₂ h₃ hA
  have hThree : Nat.card (ZMod 3) = 3 := by rw [Nat.card_eq_fintype_card, ZMod.card]
  have hp := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := T₃ A)
  rw [card_torsion h₂ h₃ hA, hThree] at hp
  exact (Nat.pow_right_injective (by decide : 1 < 3)) hp.symm

private theorem independent_pair :
    LinearIndependent (ZMod 3) ![horizontal h₂ h₃ hA D, vertical h₂ h₃ hA D] := by
  refine (linearIndependent_fin2 (K := ZMod 3)).mpr ⟨?_, ?_⟩
  · simpa using vertical_ne_zero h₂ h₃ hA D
  · intro r h
    have hx := congrArg (fun P : T₃ A => abscissa (inclusion 3 _ P)) h
    have hz : (0 : K) = D.x := by
      simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, abscissa_horizontal,
        abscissa_smul_vertical] using hx
    exact D.x_ne hz.symm

def basis : Module.Basis (Fin 2) (ZMod 3) (T₃ A) :=
  letI := finite_torsion h₂ h₃ hA
  basisOfLinearIndependentOfCardEqFinrank (independent_pair h₂ h₃ hA D)
    (by rw [finrank_torsion h₂ h₃ hA, Fintype.card_fin])

@[simp] theorem basis_zero : basis h₂ h₃ hA D 0 = horizontal h₂ h₃ hA D := by
  simp [basis, coe_basisOfLinearIndependentOfCardEqFinrank]

@[simp] theorem basis_one : basis h₂ h₃ hA D 1 = vertical h₂ h₃ hA D := by
  simp [basis, coe_basisOfLinearIndependentOfCardEqFinrank]

end
end ManuscriptAudit.CubicThreeTorsionBasis

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicThreeTorsionBasis.flexPair_nonempty,
      ``ManuscriptAudit.CubicThreeTorsionBasis.ordinate_nonvertical_sum,
      ``ManuscriptAudit.CubicThreeTorsionBasis.card_torsion,
      ``ManuscriptAudit.CubicThreeTorsionBasis.finrank_torsion,
      ``ManuscriptAudit.CubicThreeTorsionBasis.basis_zero,
      ``ManuscriptAudit.CubicThreeTorsionBasis.basis_one] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
