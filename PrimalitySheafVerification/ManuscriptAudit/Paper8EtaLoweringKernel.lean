import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaPositiveCriticalRigidity

/-! The actual positive eta eigenfunction lies in the critical lowering kernel. -/

namespace ManuscriptAudit.Paper8EtaLoweringKernel

open MaassLaplacian Paper8EtaPositiveCriticalRigidity
open Paper8NegativeHalfMaassFactorization

noncomputable section

theorem lowering_weighted_eta (x y : ℝ) (hy : 0 < y) :
    lowering (weighted (1 / 4) ModularForm.eta) x y = 0 := by
  let A : ℂ := (y ^ (1 / 4 : ℝ) : ℝ)
  let B : ℂ := (y ^ ((1 / 4 : ℝ) - 1) : ℝ)
  let E := ModularForm.eta (complexPoint x y)
  let d := deriv ModularForm.eta (complexPoint x y)
  have hη : HasDerivAt ModularForm.eta d (complexPoint x y) :=
    (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet
      (by simpa only [complexPoint_im] using hy)).hasDerivAt
  have hDx : partialX (weighted (1 / 4) ModularForm.eta) x y = A * d :=
    ((horizontal_derivative hη).const_mul A).deriv
  have hP : HasDerivAt (fun t : ℝ => ((t ^ (1 / 4 : ℝ) : ℝ) : ℂ)) ((1 / 4 : ℂ) * B) y := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, B]
      using (Real.hasDerivAt_rpow_const (p := (1 / 4 : ℝ)) (Or.inl hy.ne')).ofReal_comp
  have hDy : partialY (weighted (1 / 4) ModularForm.eta) x y =
      (1 / 4 : ℂ) * B * E + A * (Complex.I * d) := by
    have hFun : weighted (1 / 4) ModularForm.eta x =
        (fun t : ℝ => ((t ^ (1 / 4 : ℝ) : ℝ) : ℂ)) *
          (fun t : ℝ => ModularForm.eta (complexPoint x t)) := by
      funext t
      rfl
    rw [partialY, hFun]
    exact (hP.mul (vertical_derivative hη)).deriv
  have hShift : (y : ℂ) * B = A := by
    have h := Real.rpow_add hy 1 ((1 / 4 : ℝ) - 1)
    rw [show (1 : ℝ) + ((1 / 4 : ℝ) - 1) = 1 / 4 by ring, Real.rpow_one] at h
    simpa only [A, B, Complex.ofReal_mul] using congrArg Complex.ofReal h.symm
  rw [lowering, hDx, hDy]
  change -Complex.I * (y : ℂ) * (A * d) + (y : ℂ) *
    ((1 / 4 : ℂ) * B * E + A * (Complex.I * d)) - (1 / 4 : ℂ) * (A * E) = 0
  linear_combination ((1 / 4 : ℂ) * E) * hShift

end
end ManuscriptAudit.Paper8EtaLoweringKernel

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8EtaLoweringKernel.lowering_weighted_eta
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
