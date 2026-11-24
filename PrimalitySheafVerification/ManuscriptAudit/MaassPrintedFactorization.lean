import Lean.Util.CollectAxioms
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.MaassLaplacian

/-!
# The printed raising and lowering identities

Paper 9, physical PDF p. 409, equation (1.17). Express the printed
Wirtinger derivatives in real coordinates. The compositions have a
common first-order height term, which is visible on the smooth height function.
-/

namespace ManuscriptAudit.MaassPrintedFactorization

open Filter Set MaassLaplacian
open scoped Topology

noncomputable section

/-- The printed raising operator, with the Wirtinger derivative expanded. -/
def printedRaising (k : ℝ) (F : ℝ → ℝ → ℂ) (x y : ℝ) : ℂ :=
  Complex.I * partialX F x y + partialY F x y + (k : ℂ) * (y : ℂ)⁻¹ * F x y

/-- The printed lowering operator, which has the same formula at every weight. -/
def printedLowering (F : ℝ → ℝ → ℂ) (x y : ℝ) : ℂ :=
  -Complex.I * (y : ℂ) ^ 2 * partialX F x y + (y : ℂ) ^ 2 * partialY F x y

def heightMode (_x y : ℝ) : ℂ := (y : ℂ)

private theorem realCastDerivative (y : ℝ) :
    HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) y := by
  simpa only [id_eq, Complex.ofReal_one] using! (hasDerivAt_id y).ofReal_comp

private theorem realCastSquareDerivative (y : ℝ) :
    HasDerivAt (fun t : ℝ => (t : ℂ) ^ 2) (2 * (y : ℂ)) y := by
  have h := (realCastDerivative y).mul (realCastDerivative y)
  change HasDerivAt (fun t : ℝ => (t : ℂ) * (t : ℂ))
    ((1 : ℂ) * (y : ℂ) + (y : ℂ) * 1) y at h
  simpa only [pow_two, one_mul, mul_one, ← two_mul] using h

private theorem partialX_height (x y : ℝ) : partialX heightMode x y = 0 := by
  simp [partialX, heightMode]

private theorem partialY_height (x y : ℝ) : partialY heightMode x y = 1 :=
  (realCastDerivative y).deriv

private theorem raising_height (k x y : ℝ) (hy : 0 < y) :
    printedRaising k heightMode x y = 1 + (k : ℂ) := by
  have hyC : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  simp only [printedRaising, partialX_height, partialY_height, heightMode, mul_zero,
    zero_add, mul_assoc, inv_mul_cancel₀ hyC, mul_one]

private theorem lowering_height :
    printedLowering heightMode = fun _x y : ℝ => (y : ℂ) ^ 2 := by
  funext x y
  simp only [printedLowering, partialX_height, partialY_height, mul_zero, mul_one, zero_add]

private theorem lowering_raising_height (k x y : ℝ) (hy : 0 < y) :
    printedLowering (printedRaising k heightMode) x y = 0 := by
  have hx : partialX (printedRaising k heightMode) x y = 0 := by
    change deriv (fun t : ℝ => printedRaising k heightMode t y) x = 0
    simp only [raising_height k _ y hy, deriv_const]
  have hv : partialY (printedRaising k heightMode) x y = 0 := by
    have h : (fun t : ℝ => printedRaising k heightMode x t) =ᶠ[𝓝 y]
        (fun _ => (1 : ℂ) + (k : ℂ)) := by
      filter_upwards [Ioi_mem_nhds hy] with t ht
      exact raising_height k x t (Set.mem_Ioi.mp ht)
    change deriv (fun t : ℝ => printedRaising k heightMode x t) y = 0
    rw [h.deriv_eq, deriv_const]
  simp only [printedLowering, hx, hv, mul_zero, add_zero]

private theorem raising_lowering_height (k x y : ℝ) (hy : 0 < y) :
    printedRaising (k - 2) (printedLowering heightMode) x y = (k : ℂ) * (y : ℂ) := by
  have hx : partialX (fun _x t : ℝ => (t : ℂ) ^ 2) x y = 0 := by simp [partialX]
  have hv : partialY (fun _x t : ℝ => (t : ℂ) ^ 2) x y = 2 * (y : ℂ) := by
    change deriv (fun t : ℝ => (t : ℂ) ^ 2) y = 2 * (y : ℂ)
    exact (realCastSquareDerivative y).deriv
  have hyC : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hCancel : (y : ℂ)⁻¹ * (y : ℂ) ^ 2 = (y : ℂ) := by
    rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hyC, one_mul]
  rw [lowering_height, printedRaising, hx, hv]
  simp only [mul_zero, zero_add, mul_assoc, hCancel, Complex.ofReal_sub, Complex.ofReal_ofNat]
  ring

private theorem delta_height (k x y : ℝ) : maassDelta k heightMode x y = 0 := by
  have hxx : partialX (partialX heightMode) x y = 0 := by
    change deriv (fun t : ℝ => partialX heightMode t y) x = 0
    simp only [partialX_height, deriv_const]
  have hyy : partialY (partialY heightMode) x y = 0 := by
    change deriv (fun t : ℝ => partialY heightMode x t) y = 0
    simp only [partialY_height, deriv_const]
  simp only [maassDelta, hxx, hyy, zero_add, mul_zero, add_zero, partialX_height]

/-- The printed compositions at the smooth height function are both k·y
after the displayed scalar correction, while its printed Laplacian is zero. -/
theorem printed_factorizations_on_height (k x y : ℝ) (hy : 0 < y) :
    -maassDelta k heightMode x y = 0 ∧
    printedLowering (printedRaising k heightMode) x y + (k : ℂ) * heightMode x y =
        (k : ℂ) * (y : ℂ) ∧
    printedRaising (k - 2) (printedLowering heightMode) x y = (k : ℂ) * (y : ℂ) := by
  refine ⟨?_, ?_, raising_lowering_height k x y hy⟩
  · rw [delta_height, neg_zero]
  · rw [lowering_raising_height k x y hy, zero_add, heightMode]

/-- At weight 1/2 the two local factorizations in (1.17) both fail. -/
theorem printed_factorizations_fail_at_half :
    -maassDelta (1 / 2) heightMode 0 1 ≠
        printedLowering (printedRaising (1 / 2) heightMode) 0 1 +
          ((1 / 2 : ℝ) : ℂ) * heightMode 0 1 ∧
    -maassDelta (1 / 2) heightMode 0 1 ≠
        printedRaising (1 / 2 - 2) (printedLowering heightMode) 0 1 := by
  have h := printed_factorizations_on_height (1 / 2) 0 1 zero_lt_one
  rw [h.1, h.2.1, h.2.2]
  norm_num [Complex.ofReal_div]

set_option maxHeartbeats 600000 in
/-- For the printed raising/lowering convention, the two compositions
have a shared extra height-derivative term. The hypotheses express
differentiability of the six coordinate slices used in the calculation
and equality of the mixed derivatives at the point. -/
theorem printed_factorizations_eq_add_height_derivative
    (k : ℝ) (F : ℝ → ℝ → ℂ) (x y : ℝ) (hy : 0 < y)
    (hFx : DifferentiableAt ℝ (fun t : ℝ => F t y) x)
    (hFy : DifferentiableAt ℝ (fun t : ℝ => F x t) y)
    (hXX : DifferentiableAt ℝ (fun t : ℝ => partialX F t y) x)
    (hXY : DifferentiableAt ℝ (fun t : ℝ => partialY F t y) x)
    (hYX : DifferentiableAt ℝ (fun t : ℝ => partialX F x t) y)
    (hYY : DifferentiableAt ℝ (fun t : ℝ => partialY F x t) y)
    (hMixed : partialX (partialY F) x y = partialY (partialX F) x y) :
    (printedLowering (printedRaising k F) x y + (k : ℂ) * F x y =
      -maassDelta k F x y + (k : ℂ) * (y : ℂ) * partialY F x y) ∧
    (printedRaising (k - 2) (printedLowering F) x y =
      -maassDelta k F x y + (k : ℂ) * (y : ℂ) * partialY F x y) := by
  have hInv : HasDerivAt (fun t : ℝ => (t : ℂ)⁻¹) (-((y : ℂ) ^ 2)⁻¹) y := by
    simpa only [Complex.ofReal_neg, Complex.ofReal_inv, Complex.ofReal_pow] using
      (hasDerivAt_inv hy.ne').ofReal_comp
  have hSq := realCastSquareDerivative y
  have hRX : partialX (printedRaising k F) x y =
      Complex.I * partialX (partialX F) x y + partialX (partialY F) x y +
        (k : ℂ) * (y : ℂ)⁻¹ * partialX F x y :=
    (((hXX.hasDerivAt.const_mul Complex.I).add hXY.hasDerivAt).add
      (hFx.hasDerivAt.const_mul ((k : ℂ) * (y : ℂ)⁻¹))).deriv
  have hRY : partialY (printedRaising k F) x y =
      Complex.I * partialY (partialX F) x y + partialY (partialY F) x y +
        ((k : ℂ) * (-((y : ℂ) ^ 2)⁻¹) * F x y +
          (k : ℂ) * (y : ℂ)⁻¹ * partialY F x y) :=
    (((hYX.hasDerivAt.const_mul Complex.I).add hYY.hasDerivAt).add
      ((hInv.const_mul (k : ℂ)).mul hFy.hasDerivAt)).deriv
  have hLX : partialX (printedLowering F) x y =
      -Complex.I * (y : ℂ) ^ 2 * partialX (partialX F) x y +
        (y : ℂ) ^ 2 * partialX (partialY F) x y :=
    ((hXX.hasDerivAt.const_mul (-Complex.I * (y : ℂ) ^ 2)).add
      (hXY.hasDerivAt.const_mul ((y : ℂ) ^ 2))).deriv
  have hLY : partialY (printedLowering F) x y =
      (-Complex.I * (2 * (y : ℂ)) * partialX F x y +
        -Complex.I * (y : ℂ) ^ 2 * partialY (partialX F) x y) +
      (2 * (y : ℂ) * partialY F x y + (y : ℂ) ^ 2 * partialY (partialY F) x y) :=
    (((hSq.const_mul (-Complex.I)).mul hYX.hasDerivAt).add
      (hSq.mul hYY.hasDerivAt)).deriv
  have hyC : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  let expression : ℂ :=
    -(Complex.I ^ 2) * (y : ℂ) ^ 2 * partialX (partialX F) x y +
      (y : ℂ) ^ 2 * partialY (partialY F) x y -
      Complex.I * (k : ℂ) * (y : ℂ) * partialX F x y +
      (k : ℂ) * (y : ℂ) * partialY F x y
  have hLeft : printedLowering (printedRaising k F) x y + (k : ℂ) * F x y =
      expression := by
    rw [printedLowering, hRX, hRY, hMixed]
    dsimp only [expression]
    field_simp [hyC] <;> ring
  have hRight : printedRaising (k - 2) (printedLowering F) x y = expression := by
    rw [printedRaising, hLX, hLY, hMixed]
    simp only [printedLowering, expression, Complex.ofReal_sub, Complex.ofReal_ofNat]
    field_simp [hyC] <;> ring
  have hExpression :
      expression = -maassDelta k F x y + (k : ℂ) * (y : ℂ) * partialY F x y := by
    dsimp only [expression]
    rw [Complex.I_sq, maassDelta]
    ring
  exact ⟨hLeft.trans hExpression, hRight.trans hExpression⟩

end

end ManuscriptAudit.MaassPrintedFactorization

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.MaassPrintedFactorization.printed_factorizations_on_height,
      ``ManuscriptAudit.MaassPrintedFactorization.printed_factorizations_fail_at_half,
      ``ManuscriptAudit.MaassPrintedFactorization.printed_factorizations_eq_add_height_derivative] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
