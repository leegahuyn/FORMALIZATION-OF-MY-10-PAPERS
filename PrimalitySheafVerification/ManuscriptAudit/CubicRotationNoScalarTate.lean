import Lean.Util.CollectAxioms
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Tactic.Linarith
import PrimalitySheafVerification.ManuscriptAudit.CubicGenericRotationHeight
import PrimalitySheafVerification.ManuscriptAudit.CubicNaturalKernelDegree
import PrimalitySheafVerification.ManuscriptAudit.PowerTateEvaluationSurjective

/-! A genuine primitive cube rotation is never scalar on a rank-two geometric Tate module. -/

namespace ManuscriptAudit.CubicRotationNoScalarTate

open Module CubicNonsplitThreeAdicTrace CubicGenericPointHeight CubicGenericSecantHeight
open CubicNaturalPointEnd CubicNaturalCMOperations CubicNaturalShiftedRotation
open CubicGenericRotationHeight CubicNaturalKernelDegree
open PowerTorsionTower PowerTateModule PowerTateEvaluationSurjective TorsionFrobeniusModule
open scoped Padic

noncomputable section

private theorem balanced_bound {m : ℕ} [NeZero m] (hm : 4 ≤ m) (v : ZMod m) :
    2 * (v.valMinAbs ^ 2 + v.valMinAbs + 1) < (m : ℤ) ^ 2 := by
  let c := v.valMinAbs
  obtain ⟨h₁, h₂⟩ := ZMod.valMinAbs_mem_Ioc v
  change -(m : ℤ) < c * 2 at h₁
  change c * 2 ≤ (m : ℤ) at h₂
  have hm' : (4 : ℤ) ≤ m := by exact_mod_cast hm
  have hSquare : 0 ≤ ((m : ℤ) - 2 * c) * ((m : ℤ) + 2 * c) :=
    mul_nonneg (by linarith) (by linarith)
  have hmSquare : 0 ≤ ((m : ℤ) - 4) * ((m : ℤ) + 2) :=
    mul_nonneg (by linarith) (by linarith)
  change 2 * (c ^ 2 + c + 1) < (m : ℤ) ^ 2
  nlinarith

universe u

variable (L : Type u) [Field L] [IsAlgClosed L] [DecidableEq L] {A z : L}

/-- Reduction of a hypothetical scalar modulo l² would put all of E[l²] in the
kernel of [c]−ρ, whose generic height permits strictly fewer points. -/
theorem rotation_not_scalar (h₂ : (2 : L) ≠ 0) (h₃ : (3 : L) ≠ 0) (hA : A ≠ 0)
    (hz : z ^ 3 = 1) (hz₁ : z ≠ 1) (l : ℕ) [Fact l.Prime]
    (B : Basis (Fin 2) (ZMod (l ^ 1)) (PowerTorsion l (GeometricPoints L L A) 1))
    (hDiv : Function.Surjective (fun P : GeometricPoints L L A => l • P))
    (hCard : Nat.card (PowerTorsion l (GeometricPoints L L A) 2) = (l ^ 2) ^ 2) :
    ¬ ∃ w : ℤ_[l], endMap l ((rotation h₂ h₃ hA hz).atField L) =
      w • (1 : Module.End ℤ_[l] (Tate l (GeometricPoints L L A))) := by
  rintro ⟨w, hw⟩
  let G := GeometricPoints L L A
  let r := (rotation h₂ h₃ hA hz).atField L
  let m := l ^ 2
  have hl : l.Prime := Fact.out
  letI : NeZero m := ⟨pow_ne_zero _ hl.ne_zero⟩
  let v : ZMod m := PadicInt.toZModPow 2 w
  let c := v.valMinAbs
  let D := shifted h₂ h₃ hA hz c
  have hRed := scalar_reduction l G B hDiv r w hw 2
  have hPoint (P : PowerTorsion l G 2) : r P.val = c • P.val := by
    have he := congrArg (fun f : Module.End (ZMod m) (PowerTorsion l G 2) => f P) hRed
    change mapLinear m r P = v • P at he
    have hv : (c : ZMod m) = v := ZMod.coe_valMinAbs v
    rw [← hv, Int.cast_smul_eq_zsmul (ZMod m) c P] at he
    exact congrArg Subtype.val he
  let j (P : PowerTorsion l G 2) : (D.atField L).ker := ⟨P.val, by
    change c • P.val - r P.val = 0
    rw [hPoint, sub_self]⟩
  have hj : Function.Injective j := fun _ _ he => Subtype.ext (congrArg Subtype.val he)
  have hHeight := shifted_height h₂ h₃ hA hz hz₁ c
  have hPos : 0 < c ^ 2 + c + 1 := by nlinarith [sq_nonneg (2 * c + 1)]
  have hH : height A (antiInvariantApply D (genericAntiPoint A h₂ h₃ hA)) ≠ 0 := by
    intro h
    change (height A (antiInvariantApply D (genericAntiPoint A h₂ h₃ hA)) : ℤ) = _ at hHeight
    rw [h, Nat.cast_zero] at hHeight
    exact hPos.ne' hHeight.symm
  have hBound := card_of_injection_le D h₂ h₃ hA hH j hj
  change Nat.card (PowerTorsion l G 2) ≤ _ at hBound
  rw [hCard] at hBound
  have hBound' : (m : ℤ) ^ 2 ≤ 2 *
      (height A (antiInvariantApply D (genericAntiPoint A h₂ h₃ hA)) : ℤ) := by
    exact_mod_cast hBound
  have hm : 4 ≤ m := by
    change 2 ^ 2 ≤ l ^ 2
    exact Nat.pow_le_pow_left hl.two_le 2
  rw [hHeight] at hBound'
  exact (not_lt_of_ge hBound') (balanced_bound hm v)

end

end ManuscriptAudit.CubicRotationNoScalarTate

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicRotationNoScalarTate.rotation_not_scalar
  let allowed : List Name := [``propext, `Classical.choice, `Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
