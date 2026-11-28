import Lean.Util.CollectAxioms
import Mathlib.Analysis.RCLike.Sqrt
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaPositiveLowerLeftMultiplier
import PrimalitySheafVerification.ManuscriptAudit.Paper8ActualEtaSquaredModularity

/-! Positive lower-row entries give the exact right-inversion phase of the principal eta multiplier. -/

namespace ManuscriptAudit.Paper8EtaDedekindInversion

open Set Matrix UpperHalfPlane
open Paper8EtaPositiveLowerLeftMultiplier Paper8ActualEtaSquaredModularity
open scoped MatrixGroups

theorem right_S_entries (g : SL(2, ℤ)) :
    (g * ModularGroup.S) 1 0 = g 1 1 ∧ (g * ModularGroup.S) 1 1 = -g 1 0 := by
  change (g.1 * ModularGroup.S.1) 1 0 = g 1 1 ∧
    (g.1 * ModularGroup.S.1) 1 1 = -g 1 0
  rw [ModularGroup.coe_S]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem sqrt_I_mul {w : ℂ} (hw : 0 < w.re) (hi : 0 ≤ w.im) :
    Complex.sqrt (Complex.I * w) = Complex.sqrt Complex.I * Complex.sqrt w := by
  have hw0 : w ≠ 0 := fun h => hw.ne' (by simpa only [h, Complex.zero_re])
  have hArg := Complex.arg_lt_pi_div_two_iff.2 (Or.inl hw)
  have hLo := Complex.arg_nonneg_iff.2 hi
  have hRange : Complex.I.arg + w.arg ∈ Ioc (-Real.pi) Real.pi := by
    rw [Complex.arg_I]
    exact ⟨by linarith [Real.pi_pos], by linarith⟩
  rw [sqrt_eq_exp (mul_ne_zero Complex.I_ne_zero hw0), sqrt_eq_exp Complex.I_ne_zero,
    sqrt_eq_exp hw0, Complex.log_mul Complex.I_ne_zero hw0 hRange, add_div, Complex.exp_add]

theorem principalEtaMultiplier_mul_S (g : SL(2, ℤ)) (hc : 0 < g 1 0) (hd : 0 < g 1 1) :
    principalEtaMultiplier (g * ModularGroup.S) =
      principalEtaMultiplier g / Complex.sqrt Complex.I := by
  let z : ℍ := ⟨Complex.I, by simp⟩
  let w : ℂ := (g 1 1 : ℂ) + (g 1 0 : ℂ) * Complex.I
  obtain ⟨hC, hD⟩ := right_S_entries g
  have hS : ModularGroup.S • z = z := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.modular_S_smul]
    change -Complex.I⁻¹ = Complex.I
    simp [Complex.inv_I]
  have hW : denominator g z = w := by unfold denominator w z; ring
  have hSW : denominator (g * ModularGroup.S) z = Complex.I * w := by
    unfold denominator w
    rw [hC, hD, Int.cast_neg]
    change (g 1 1 : ℂ) * Complex.I + -(g 1 0 : ℂ) =
      Complex.I * ((g 1 1 : ℂ) + (g 1 0 : ℂ) * Complex.I)
    linear_combination -(g 1 0 : ℂ) * Complex.I_sq
  have hRe : 0 < w.re := by
    have h : 0 < (g 1 1 : ℝ) := by exact_mod_cast hd
    simpa [w, Complex.add_re, Complex.mul_re] using h
  have hIm : 0 ≤ w.im := by
    have h : 0 ≤ (g 1 0 : ℝ) := by exact_mod_cast hc.le
    simpa [w, Complex.add_im, Complex.mul_im] using h
  have hSq := sqrt_I_mul hRe hIm
  have hZ : ModularForm.eta z ≠ 0 := ModularForm.eta_ne_zero z.im_pos
  have hInd : 0 < (g * ModularGroup.S) 1 0 := by rwa [hC]
  have hE := eta_principal_transform g hc z
  have hES := eta_principal_transform (g * ModularGroup.S) hInd z
  rw [mul_smul, hS, hSW, hSq] at hES
  rw [hW] at hE
  have hEq : (principalEtaMultiplier (g * ModularGroup.S) * Complex.sqrt Complex.I) *
        (Complex.sqrt w * ModularForm.eta z) =
      principalEtaMultiplier g * (Complex.sqrt w * ModularForm.eta z) := by
    calc
      _ = ModularForm.eta (g • z : ℍ) := by rw [hES]; ring
      _ = _ := by rw [hE]; ring
  have hQ : Complex.sqrt w ≠ 0 := by
    rw [sqrt_eq_exp (hW ▸ denominator_ne_zero g z)]
    exact Complex.exp_ne_zero _
  have hI : Complex.sqrt Complex.I ≠ 0 := by
    rw [sqrt_eq_exp Complex.I_ne_zero]
    exact Complex.exp_ne_zero _
  exact (eq_div_iff hI).2 (mul_right_cancel₀ (mul_ne_zero hQ hZ) hEq)

end ManuscriptAudit.Paper8EtaDedekindInversion

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8EtaDedekindInversion.principalEtaMultiplier_mul_S
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
