import Lean.Util.CollectAxioms
import Mathlib.Tactic.LinearCombination
import PrimalitySheafVerification.ManuscriptAudit.Paper8MaassGaugeDerivative

/-! The exact first-order odd Maass raising operator after division by the actual eta gauge. -/

namespace ManuscriptAudit.Paper8MaassGaugeRaising

open Set Filter UpperHalfPlane
open MaassLaplacian Paper8NegativeHalfMaassFactorization Paper8MaassCriticalHolomorphic
open Paper8MaassEtaGauge Paper8MaassGaugeDerivative Paper8MaassWirtinger
open scoped Topology

noncomputable section

private theorem gauge_weighted_conj (x y : ℝ) :
    realProfile complexGauge x y =
      weighted (1 / 4) (fun w => (starRingEnd ℂ) (ModularForm.eta w)) x y := by
  simp only [realProfile, complexGauge, complexPoint_im] <;> rfl

theorem raising_complexGauge (x y : ℝ) (hy : 0 < y) :
    raising (realProfile complexGauge) x y = 0 := by
  let H := weighted (1 / 4) (fun w => (starRingEnd ℂ) (ModularForm.eta w))
  have hH : realProfile complexGauge = H := by funext u v; exact gauge_weighted_conj u v
  rw [hH]
  let A : ℂ := (y ^ (1 / 4 : ℝ) : ℝ)
  let B : ℂ := (y ^ ((1 / 4 : ℝ) - 1) : ℝ)
  let E := (starRingEnd ℂ) (ModularForm.eta (complexPoint x y))
  let d := deriv ModularForm.eta (complexPoint x y)
  have hη : HasDerivAt ModularForm.eta d (complexPoint x y) :=
    (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet
      (by simpa only [complexPoint_im] using hy)).hasDerivAt
  have hEtaX := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt x
    (horizontal_derivative hη)
  have hEtaY : HasDerivAt (fun t : ℝ => (starRingEnd ℂ) (ModularForm.eta (complexPoint x t)))
      (-Complex.I * ((starRingEnd ℂ) d)) y := by
    have hV := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt y (vertical_derivative hη)
    change HasDerivAt (fun t : ℝ => (starRingEnd ℂ) (ModularForm.eta (complexPoint x t)))
      ((starRingEnd ℂ) (Complex.I * d)) y at hV
    simpa only [map_mul, Complex.conj_I] using hV
  have hDx : partialX H x y = A * (starRingEnd ℂ) d :=
    (hEtaX.const_mul A).deriv
  have hP : HasDerivAt (fun t : ℝ => ((t ^ (1 / 4 : ℝ) : ℝ) : ℂ)) ((1 / 4 : ℂ) * B) y := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, B]
      using (Real.hasDerivAt_rpow_const (p := (1 / 4 : ℝ)) (Or.inl hy.ne')).ofReal_comp
  have hDy : partialY H x y =
      (1 / 4 : ℂ) * B * E + A * (-Complex.I * (starRingEnd ℂ) d) := by
    have hFun : H x = (fun t : ℝ => ((t ^ (1 / 4 : ℝ) : ℝ) : ℂ)) *
        (fun t : ℝ => (starRingEnd ℂ) (ModularForm.eta (complexPoint x t))) := by
      funext t
      rfl
    rw [partialY, hFun]
    exact (hP.mul hEtaY).deriv
  have hShift : (y : ℂ) * B = A := by
    have h := Real.rpow_add hy 1 ((1 / 4 : ℝ) - 1)
    rw [show (1 : ℝ) + ((1 / 4 : ℝ) - 1) = 1 / 4 by ring, Real.rpow_one] at h
    simpa only [A, B, Complex.ofReal_mul] using congrArg Complex.ofReal h.symm
  rw [raising, hDx, hDy]
  change Complex.I * (y : ℂ) * (A * (starRingEnd ℂ) d) + (y : ℂ) *
    ((1 / 4 : ℂ) * B * E + A * (-Complex.I * (starRingEnd ℂ) d)) - (1 / 4 : ℂ) * (A * E) = 0
  linear_combination ((1 / 4 : ℂ) * E) * hShift

theorem raising_eq_gauge_derivativeZ {F : ℂ → ℂ} (x y : ℝ) (hy : 0 < y)
    (hF : DifferentiableAt ℝ F (complexPoint x y)) :
    raising (realProfile F) x y =
      2 * Complex.I * (y : ℂ) * complexGauge (complexPoint x y) *
        derivativeZ (complexGaugeRatio F) (complexPoint x y) := by
  let z : ℍ := ⟨complexPoint x y, by simpa only [complexPoint_im] using hy⟩
  let A := realProfile complexGauge
  let B := realProfile (complexGaugeRatio F)
  let G : Profile := fun u v => A u v * B u v
  have hEq (u v : ℝ) (hv : 0 < v) : realProfile F u v = G u v := by
    let w : ℍ := ⟨complexPoint u v, by simpa only [complexPoint_im] using hv⟩
    have hn : complexGauge (complexPoint u v) ≠ 0 := by
      change complexGauge (w : ℂ) ≠ 0
      rw [complexGauge_coe]
      exact etaGauge_ne_zero w
    simp only [G, A, B, realProfile, complexGaugeRatio]
    field_simp [hn] <;> ring
  have hX : partialX (realProfile F) x y = partialX G x y := by
    unfold partialX
    exact congrArg (fun f : ℝ → ℂ => deriv f x) (funext fun u => hEq u y hy)
  have hY : partialY (realProfile F) x y = partialY G x y := by
    have hLocal : realProfile F x =ᶠ[𝓝 y] G x :=
      (Ioi_mem_nhds hy).mono (fun t ht => hEq x t ht)
    exact hLocal.deriv_eq
  have hA : DifferentiableAt ℝ complexGauge z := complexGauge_differentiableAt z
  have hB : DifferentiableAt ℝ (complexGaugeRatio F) z := complexGaugeRatio_differentiableAt z hF
  have hLineX : DifferentiableAt ℝ (fun t : ℝ => complexPoint t y) x := by unfold complexPoint; fun_prop
  have hLineY : DifferentiableAt ℝ (fun t : ℝ => complexPoint x t) y := by unfold complexPoint; fun_prop
  have hProd := raising_mul A B x y (hA.comp x hLineX) (hA.comp y hLineY)
    (hB.comp x hLineX) (hB.comp y hLineY)
  have hRaise : raising (realProfile F) x y = raising G x y := by
    rw [raising, raising, hX, hY, hEq x y hy]
  rw [hRaise]
  change raising (fun u v => A u v * B u v) x y = _
  rw [hProd, show raising A x y = 0 from raising_complexGauge x y hy, mul_zero, zero_add]
  rw [derivativeZ_eq_partials hB]
  unfold raisingDerivative
  change complexGauge (complexPoint x y) *
      (Complex.I * (y : ℂ) * partialX B x y + (y : ℂ) * partialY B x y) = _
  linear_combination ((y : ℂ) * complexGauge (complexPoint x y) * partialY B x y) * Complex.I_sq

end
end ManuscriptAudit.Paper8MaassGaugeRaising

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8MaassGaugeRaising.raising_complexGauge,
      ``ManuscriptAudit.Paper8MaassGaugeRaising.raising_eq_gauge_derivativeZ] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
