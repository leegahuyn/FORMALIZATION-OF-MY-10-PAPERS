import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import PrimalitySheafVerification.ManuscriptAudit.CubicNaturalCMOperations
import PrimalitySheafVerification.ManuscriptAudit.CubicNaturalPointEndProduct
import PrimalitySheafVerification.ManuscriptAudit.EisensteinCharacteristicFactorization
import PrimalitySheafVerification.ManuscriptAudit.CubicFrobeniusTranscendentalRelation
import PrimalitySheafVerification.ManuscriptAudit.CubicJacobiEisenstein

/-! At every split finite field, actual centered-cubic Frobenius is one of the two integral Jacobi orientations. -/

namespace ManuscriptAudit.CubicSplitIntegralFrobenius

open FiniteFieldPointCount CubicThreeTorsionCard CubicNonsplitThreeAdicTrace
open CubicNaturalPointEnd CubicNaturalCMOperations RotationNormUnit
open CubicGenericFunctionField CubicGenericAntiInvariant CubicGenericCharacteristicRelation
open CubicFrobeniusTranscendentalRelation EisensteinCharacteristicFactorization

noncomputable section
open scoped Classical

universe u

variable {K L : Type u} [Field K] [Fintype K] [Field L] [DecidableEq L] [Algebra K L]
  [IsAlgClosed L]

/-- The actual relative Frobenius equals an integral linear combination of the identity
and the chosen base-defined rotation, with trace and norm determined by arithmetic. -/
theorem exists_integral_combination (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (hchar : ringChar K ≠ 2) (hsplit : 3 ∣ Fintype.card K - 1)
    {A z : K} (hA : A ≠ 0) (hz : z ^ 3 = 1) (hz₁ : z ≠ 1) :
    ∃ a b : ℤ,
      arithmeticTrace K A = 2 * a - b ∧
      a ^ 2 - a * b + b ^ 2 = (Fintype.card K : ℤ) ∧
      arithmeticPointFrobenius K L A =
        combination ((rotation h₂ h₃ hA hz).atField L) a b := by
  obtain ⟨a, b, hTrace, hNorm⟩ := CubicJacobiEisenstein.exists_integral_trace_norm hchar
    hsplit hA (shortCubic_discriminant_ne_zero h₂ h₃ hA)
  have ht : arithmeticTrace K A = 2 * a - b := hTrace
  let M := Model A
  let D := difference h₂ h₃ hA hz a b
  let E := difference h₂ h₃ hA hz (a - b) (-b)
  let F := arithmeticPointFrobenius K M A
  let R := (rotation h₂ h₃ hA hz).atField M
  let Q := genericPoint A h₂ h₃ hA
  have hQuad : R ^ 2 + R + 1 = 0 := rotation_quadratic h₂ h₃ hA hz M hz₁
  have hComm : Commute F R := commutes_frobenius h₂ h₃ hA hz M
  have hProduct : (D.atField M) * (E.atField M) = characteristicError K M A := by
    change (F - combination R a b) * (F - combination R (a - b) (-b)) = _
    rw [factor F R hQuad hComm a b, ← ht, ← hNorm] <;> rfl
  have hOdd := FiniteField.odd_card_of_char_ne_two hchar
  let k := Fintype.card K / 2
  have hq : Fintype.card K = 2 * k + 1 := by dsimp only [k]; omega
  have hk : 0 < k := Nat.div_pos Fintype.one_lt_card two_pos
  have hGeneric := congrArg (fun P : antiInvariant A => P.val)
    (generic_relation_two_nsmul A hq hk h₂ h₃ hchar hA)
  have hTwo : (2 : ℕ) • D.atField M (E.atField M Q) = 0 := by
    change (2 : ℕ) • ((D.atField M) * (E.atField M)) Q = 0
    rw [hProduct, characteristicError_apply]
    exact hGeneric
  have hEither : D.atField L = 0 ∨ E.atField L = 0 :=
    eq_zero_or_eq_zero_of_composite D E h₂ h₃ hA hTwo
  rcases hEither with hD | hE
  · exact ⟨a, b, ht, hNorm.symm, sub_eq_zero.mp hD⟩
  · obtain ⟨hcTrace, hcNorm⟩ := conjugate_coefficients a b
    exact ⟨a - b, -b, ht.trans hcTrace.symm, hcNorm.trans hNorm.symm, sub_eq_zero.mp hE⟩

end

end ManuscriptAudit.CubicSplitIntegralFrobenius

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicSplitIntegralFrobenius.exists_integral_combination
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
