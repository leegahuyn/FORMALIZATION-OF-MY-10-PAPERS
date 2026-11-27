import Lean.Util.CollectAxioms
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic.LinearCombination
import PrimalitySheafVerification.ManuscriptAudit.Paper8XiShadow

/-!
# The two printed Paper 8 ξ factorizations

Physical p. 334 applies the antiholomorphic derivative with no output
conjugation. Physical pp. 303 and 336 display the conjugated derivative.
Both statements use the Laplacian with first order term
`i k y (∂ₓ + i ∂ᵧ)`. The conjugated composition is the negative of
this Laplacian when the mixed partials agree. The height function shows
the failure of both printed positive-sign formulas.
-/

namespace ManuscriptAudit.Paper8XiFactorization

open MaassLaplacian (partialX partialY)
open Paper8XiShadow (Field dBar)
open scoped ComplexConjugate

noncomputable section

private def heightPower (a y : ℝ) : ℂ := ((y ^ a : ℝ) : ℂ)

def printedDelta (k : ℝ) (F : Field) (x y : ℝ) : ℂ :=
  -((y : ℂ) ^ 2) * (partialX (partialX F) x y + partialY (partialY F) x y) +
    Complex.I * (k : ℂ) * (y : ℂ) * (partialX F x y + Complex.I * partialY F x y)

def conjugatedXi (k : ℝ) (F : Field) (x y : ℝ) : ℂ :=
  heightPower k y * (Complex.I * conj (partialX F x y) + conj (partialY F x y))

def unconjugatedXi (k : ℝ) (F : Field) (x y : ℝ) : ℂ :=
  heightPower k y * (Complex.I * partialX F x y - partialY F x y)

theorem conjugatedXi_eq_literal (k : ℝ) (F : Field) (x y : ℝ) :
    conjugatedXi k F x y = 2 * Complex.I * ((y ^ k : ℝ) : ℂ) * conj (dBar F x y) := by
  simp only [conjugatedXi, heightPower, dBar, map_div₀, map_add, map_mul, map_ofNat,
    Complex.conj_I]
  linear_combination (((y ^ k : ℝ) : ℂ) * conj (partialY F x y)) * Complex.I_sq

theorem unconjugatedXi_eq_literal (k : ℝ) (F : Field) (x y : ℝ) :
    unconjugatedXi k F x y = 2 * Complex.I * ((y ^ k : ℝ) : ℂ) * dBar F x y := by
  unfold unconjugatedXi heightPower dBar
  linear_combination -(((y ^ k : ℝ) : ℂ) * partialY F x y) * Complex.I_sq

private theorem heightPower_hasDerivAt (a : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (heightPower a) ((a : ℂ) * heightPower (a - 1) y) y := by
  change HasDerivAt (fun t : ℝ => ((t ^ a : ℝ) : ℂ))
    ((a : ℂ) * ((y ^ (a - 1) : ℝ) : ℂ)) y
  simpa only [Complex.ofReal_mul] using!
    (Real.hasDerivAt_rpow_const (p := a) (Or.inl hy.ne')).ofReal_comp

private theorem conj_heightPower (a y : ℝ) : conj (heightPower a y) = heightPower a y :=
  Complex.conj_ofReal _

private theorem heightPower_mul (a b : ℝ) {y : ℝ} (hy : 0 < y) :
    heightPower a y * heightPower b y = heightPower (a + b) y := by
  unfold heightPower
  rw [← Complex.ofReal_mul, ← Real.rpow_add hy]

private theorem heightPowers_product (k : ℝ) {y : ℝ} (hy : 0 < y) :
    heightPower (2 - k) y * heightPower k y = (y : ℂ) ^ 2 := by
  rw [heightPower_mul _ _ hy, show 2 - k + k = (2 : ℝ) by ring,
    heightPower, Real.rpow_two, Complex.ofReal_pow]

private theorem heightPowers_product_deriv (k : ℝ) {y : ℝ} (hy : 0 < y) :
    heightPower (2 - k) y * heightPower (k - 1) y = (y : ℂ) := by
  rw [heightPower_mul _ _ hy, show 2 - k + (k - 1) = (1 : ℝ) by ring,
    heightPower, Real.rpow_one]

private theorem hasDerivAt_conj {f : ℝ → ℂ} {f' : ℂ} {x : ℝ}
    (hf : HasDerivAt f f' x) : HasDerivAt (fun t => conj (f t)) (conj f') x := by
  let C : ℂ →L[ℝ] ℂ := Complex.conjCLE.toContinuousLinearMap
  have hC : HasFDerivAt C C (f x) := C.hasFDerivAt
  exact hC.comp_hasDerivAt x hf

/-- Actual coordinate derivatives give the negative of the displayed p. 336 Laplacian. -/
theorem conjugated_composition_eq_neg_delta (k : ℝ) (F : Field) {x y : ℝ} (hy : 0 < y)
    (hxx : DifferentiableAt ℝ (fun t => partialX F t y) x)
    (hyx : DifferentiableAt ℝ (fun t => partialY F t y) x)
    (hxy : DifferentiableAt ℝ (fun t => partialX F x t) y)
    (hyy : DifferentiableAt ℝ (fun t => partialY F x t) y)
    (hMixed : partialX (partialY F) x y = partialY (partialX F) x y) :
    conjugatedXi (2 - k) (conjugatedXi k F) x y = -printedDelta k F x y := by
  have hX := (((hasDerivAt_conj hxx.hasDerivAt).const_mul Complex.I).add
    (hasDerivAt_conj hyx.hasDerivAt)).const_mul (heightPower k y)
  have hY := (heightPower_hasDerivAt k hy).mul
    (((hasDerivAt_conj hxy.hasDerivAt).const_mul Complex.I).add
      (hasDerivAt_conj hyy.hasDerivAt))
  have hx : partialX (conjugatedXi k F) x y =
      heightPower k y * (Complex.I * conj (partialX (partialX F) x y) +
        conj (partialX (partialY F) x y)) := hX.deriv
  have hy' : partialY (conjugatedXi k F) x y =
      ((k : ℂ) * heightPower (k - 1) y) *
        (Complex.I * conj (partialX F x y) + conj (partialY F x y)) +
      heightPower k y * (Complex.I * conj (partialY (partialX F) x y) +
        conj (partialY (partialY F) x y)) := hY.deriv
  change heightPower (2 - k) y * (Complex.I * conj (partialX (conjugatedXi k F) x y) +
    conj (partialY (conjugatedXi k F) x y)) = _
  calc
    _ = heightPower (2 - k) y * heightPower k y *
        (partialX (partialX F) x y + partialY (partialY F) x y) +
        heightPower (2 - k) y * heightPower (k - 1) y *
          ((k : ℂ) * (-Complex.I * partialX F x y + partialY F x y)) := by
      rw [hx, hy']
      simp only [map_mul, map_add, conj_heightPower, Complex.conj_ofReal, Complex.conj_I,
        Complex.conj_conj, hMixed]
      linear_combination -(heightPower (2 - k) y * heightPower k y *
        partialX (partialX F) x y) * Complex.I_sq
    _ = _ := by
      rw [heightPowers_product k hy, heightPowers_product_deriv k hy, printedDelta]
      linear_combination ((y : ℂ) * (k : ℂ) * partialY F x y) * Complex.I_sq

def heightField (_x y : ℝ) : ℂ := (y : ℂ)

private theorem realCastDerivative (y : ℝ) :
    HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) y := by
  simpa only [id_eq, Complex.ofReal_one] using (hasDerivAt_id y).ofReal_comp

private theorem partialX_height (x y : ℝ) : partialX heightField x y = 0 := by
  simp [partialX, heightField]

private theorem partialY_height (x y : ℝ) : partialY heightField x y = 1 :=
  (realCastDerivative y).deriv

theorem delta_height (k x y : ℝ) : printedDelta k heightField x y = -(k : ℂ) * (y : ℂ) := by
  have hxx : partialX (partialX heightField) x y = 0 := by
    simp [partialX, heightField]
  have hyy : partialY (partialY heightField) x y = 0 := by
    change deriv (fun t => partialY heightField x t) y = 0
    simp only [partialY_height, deriv_const]
  simp only [printedDelta, hxx, hyy, partialX_height, partialY_height, zero_add, mul_zero, mul_one]
  linear_combination ((k : ℂ) * (y : ℂ)) * Complex.I_sq

private theorem xi_height (k : ℝ) :
    conjugatedXi k heightField = (fun _ y => heightPower k y) ∧
      unconjugatedXi k heightField = (fun _ y => -heightPower k y) := by
  constructor <;> funext x y
  · simp only [conjugatedXi, partialX_height, partialY_height, map_zero, map_one, mul_zero,
      zero_add, mul_one]
  · simp only [unconjugatedXi, partialX_height, partialY_height, mul_zero, zero_sub, mul_neg,
      mul_one]

theorem compositions_on_height (k x y : ℝ) (hy : 0 < y) :
    conjugatedXi (2 - k) (conjugatedXi k heightField) x y = (k : ℂ) * (y : ℂ) ∧
      unconjugatedXi (2 - k) (unconjugatedXi k heightField) x y = (k : ℂ) * (y : ℂ) := by
  have hY : partialY (fun _ t => heightPower k t) x y =
      (k : ℂ) * heightPower (k - 1) y := (heightPower_hasDerivAt k hy).deriv
  have hYNeg : partialY (fun _ t => -heightPower k t) x y =
      -((k : ℂ) * heightPower (k - 1) y) := (heightPower_hasDerivAt k hy).neg.deriv
  have hX : partialX (fun _ t => heightPower k t) x y = 0 := deriv_const _ _
  have hXNeg : partialX (fun _ t => -heightPower k t) x y = 0 := deriv_const _ _
  rw [(xi_height k).1, (xi_height k).2]
  constructor
  · simp only [conjugatedXi, hX, hY, map_zero, map_mul, conj_heightPower, Complex.conj_ofReal,
      mul_zero, zero_add]
    rw [← mul_left_comm (k : ℂ), heightPowers_product_deriv k hy]
  · simp only [unconjugatedXi, hXNeg, hYNeg, mul_zero, zero_sub, neg_neg]
    rw [← mul_left_comm (k : ℂ), heightPowers_product_deriv k hy]

theorem both_printed_signs_fail_at_half :
    printedDelta (1 / 2) heightField 0 1 ≠
        conjugatedXi (2 - 1 / 2) (conjugatedXi (1 / 2) heightField) 0 1 ∧
      printedDelta (1 / 2) heightField 0 1 ≠
        unconjugatedXi (2 - 1 / 2) (unconjugatedXi (1 / 2) heightField) 0 1 := by
  obtain ⟨h₁, h₂⟩ := compositions_on_height (1 / 2) 0 1 zero_lt_one
  simp only [delta_height, h₁, h₂]
  constructor <;> norm_num [Complex.ofReal_div]

end
end ManuscriptAudit.Paper8XiFactorization

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8XiFactorization.conjugatedXi_eq_literal,
      ``ManuscriptAudit.Paper8XiFactorization.unconjugatedXi_eq_literal,
      ``ManuscriptAudit.Paper8XiFactorization.conjugated_composition_eq_neg_delta,
      ``ManuscriptAudit.Paper8XiFactorization.delta_height,
      ``ManuscriptAudit.Paper8XiFactorization.compositions_on_height,
      ``ManuscriptAudit.Paper8XiFactorization.both_printed_signs_fail_at_half] do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {axioms}"
