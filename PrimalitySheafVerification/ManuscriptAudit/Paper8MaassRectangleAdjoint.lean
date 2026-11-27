import Lean.Util.CollectAxioms
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import PrimalitySheafVerification.ManuscriptAudit.Paper8NegativeHalfMaassFactorization
import PrimalitySheafVerification.ManuscriptAudit.RectangularIntegral

/-! Green's identity for the actual raising expression at a bounded cusp rectangle. -/

namespace ManuscriptAudit.Paper8MaassRectangleAdjoint

open MeasureTheory Set
open MaassLaplacian Paper8NegativeHalfMaassFactorization RectangularIntegral

noncomputable section

def density (F G : Profile) (z : ℝ × ℝ) : ℂ :=
  star (F z.1 z.2) * G z.1 z.2 / (z.2 : ℂ)^2

private def fluxX (F G : Profile) (x y : ℝ) : ℂ :=
  (Complex.I * (y : ℂ)⁻¹) * (star (F x y) * G x y)

private def rateX (F G : Profile) (x y : ℝ) : ℂ :=
  (Complex.I * (y : ℂ)⁻¹) *
    (star (partialX F x y) * G x y + star (F x y) * partialX G x y)

private def fluxY (F G : Profile) (x y : ℝ) : ℂ :=
  (star (F x y) * G x y) * (-(y : ℂ)⁻¹)

private def rateY (F G : Profile) (x y : ℝ) : ℂ :=
  (star (partialY F x y) * G x y + star (F x y) * partialY G x y) * (-(y : ℂ)⁻¹) +
    (star (F x y) * G x y) * ((y : ℂ)^2)⁻¹

private theorem conj_deriv {f : ℝ → ℂ} {f' : ℂ} {x : ℝ}
    (hf : HasDerivAt f f' x) : HasDerivAt (fun t => star (f t)) (star f') x :=
  (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt x hf

private theorem fluxX_deriv (F G : Profile) (x y : ℝ)
    (hF : DifferentiableAt ℝ (fun t => F t y) x)
    (hG : DifferentiableAt ℝ (fun t => G t y) x) :
    HasDerivAt (fun t => fluxX F G t y) (rateX F G x y) x :=
  ((conj_deriv hF.hasDerivAt).mul hG.hasDerivAt).const_mul _

private theorem fluxY_deriv (F G : Profile) (x y : ℝ) (hy : (y : ℂ) ≠ 0)
    (hF : DifferentiableAt ℝ (F x) y)
    (hG : DifferentiableAt ℝ (G x) y) :
    HasDerivAt (fluxY F G x) (rateY F G x y) y := by
  have hyR : y ≠ 0 := by exact_mod_cast hy
  have hinv : HasDerivAt (fun t : ℝ => -(t : ℂ)⁻¹) ((y : ℂ)^2)⁻¹ y := by
    simpa [div_eq_mul_inv, neg_mul, Complex.ofReal_inv, Complex.ofReal_pow] using
      (((hasDerivAt_id y).inv hyR).neg).ofReal_comp
  exact ((conj_deriv hF.hasDerivAt).mul hG.hasDerivAt).mul hinv

private theorem density_difference (F G : Profile) (x y : ℝ) (hy : (y : ℂ) ≠ 0) :
    density F (adjointExpression G) (x, y) - density (raising F) G (x, y) =
      rateX F G x y + rateY F G x y := by
  have hq : star (1/4 : ℂ) = (1/4 : ℂ) := by
    rw [← show ((1/4 : ℝ) : ℂ) = (1/4 : ℂ) by norm_num [Complex.ofReal_div]]
    exact Complex.conj_ofReal _
  have hStarY : star (y : ℂ) = (y : ℂ) := Complex.conj_ofReal y
  have hStarI : star Complex.I = -Complex.I := Complex.conj_I
  unfold density adjointExpression raising rateX rateY
  simp only [Prod.fst, Prod.snd, star_add, star_sub, star_mul, hStarI, hStarY, hq]
  field_simp [hy] <;> ring

set_option maxHeartbeats 1600000 in
/-- The actual raising and formal adjoint expressions are adjoint on a rectangle whenever
their horizontal and vertical fluxes match on the pairs of opposite edges. -/
theorem green_identity {a b c d : ℝ} (hab : a ≤ b) (hc : 0 < c) (hcd : c ≤ d)
    (F G : Profile)
    (hF : ContinuousOn F.uncurry (rectangle a b c d))
    (hG : ContinuousOn G.uncurry (rectangle a b c d))
    (hFx : ContinuousOn (partialX F).uncurry (rectangle a b c d))
    (hFy : ContinuousOn (partialY F).uncurry (rectangle a b c d))
    (hGx : ContinuousOn (partialX G).uncurry (rectangle a b c d))
    (hGy : ContinuousOn (partialY G).uncurry (rectangle a b c d))
    (dFx : ∀ x ∈ Icc a b, ∀ y ∈ Icc c d, DifferentiableAt ℝ (fun t => F t y) x)
    (dFy : ∀ x ∈ Icc a b, ∀ y ∈ Icc c d, DifferentiableAt ℝ (F x) y)
    (dGx : ∀ x ∈ Icc a b, ∀ y ∈ Icc c d, DifferentiableAt ℝ (fun t => G t y) x)
    (dGy : ∀ x ∈ Icc a b, ∀ y ∈ Icc c d, DifferentiableAt ℝ (G x) y)
    (hx : ∀ y ∈ Icc c d, star (F b y) * G b y = star (F a y) * G a y)
    (hy : ∀ x ∈ Icc a b, star (F x d) * G x d / (d : ℂ) =
      star (F x c) * G x c / (c : ℂ)) :
    box a b c d (density F (adjointExpression G)) =
      box a b c d (density (raising F) G) := by
  have y_ne (z : ℝ × ℝ) (hz : z ∈ rectangle a b c d) : (z.2 : ℂ) ≠ 0 := by
    exact_mod_cast (hc.trans_le hz.2.1).ne'
  have hY : ContinuousOn (fun z : ℝ × ℝ => (z.2 : ℂ)) (rectangle a b c d) :=
    (Complex.continuous_ofReal.comp continuous_snd).continuousOn
  have hYi := hY.inv₀ y_ne
  have hY2i := (hY.pow 2).inv₀ (fun z hz => pow_ne_zero 2 (y_ne z hz))
  have hFC := Complex.conjCLE.continuous.comp_continuousOn hF
  have hFxC := Complex.conjCLE.continuous.comp_continuousOn hFx
  have hFyC := Complex.conjCLE.continuous.comp_continuousOn hFy
  have hRx : ContinuousOn (rateX F G).uncurry (rectangle a b c d) :=
    (continuousOn_const.mul hYi).mul ((hFxC.mul hG).add (hFC.mul hGx))
  have hRy : ContinuousOn (rateY F G).uncurry (rectangle a b c d) :=
    (((hFyC.mul hG).add (hFC.mul hGy)).mul hYi.neg).add ((hFC.mul hG).mul hY2i)
  have hAdj : ContinuousOn (adjointExpression G).uncurry (rectangle a b c d) :=
    (((continuousOn_const.mul hY).mul hGx).sub (hY.mul hGy)).add
      (continuousOn_const.mul hG)
  have hRaise : ContinuousOn (raising F).uncurry (rectangle a b c d) :=
    (((continuousOn_const.mul hY).mul hFx).add (hY.mul hFy)).sub
      (continuousOn_const.mul hF)
  have hL : ContinuousOn (density F (adjointExpression G)) (rectangle a b c d) :=
    (hFC.mul hAdj).div (hY.pow 2) (fun z hz => pow_ne_zero 2 (y_ne z hz))
  have hR : ContinuousOn (density (raising F) G) (rectangle a b c d) :=
    ((Complex.conjCLE.continuous.comp_continuousOn hRaise).mul hG).div
      (hY.pow 2) (fun z hz => pow_ne_zero 2 (y_ne z hz))
  have intX : box a b c d (rateX F G).uncurry = 0 := by
    rw [box_rows hab hcd hRx]
    calc
      (∫ y in c..d, ∫ x in a..b, rateX F G x y) = ∫ _ in c..d, (0 : ℂ) := by
        apply intervalIntegral.integral_congr
        intro y hy'
        rw [uIcc_of_le hcd] at hy'
        have hline : ContinuousOn (fun x => rateX F G x y) (uIcc a b) := by
          rw [uIcc_of_le hab]
          let line : ℝ → ℝ × ℝ := fun t => (t, y)
          have hC : Continuous line :=
            continuous_id.prodMk (continuous_const : Continuous (fun _ : ℝ => y))
          have hM : MapsTo line (Icc a b) (rectangle a b c d) :=
            fun _ ht => ⟨ht, hy'⟩
          change ContinuousOn ((rateX F G).uncurry ∘ line) (Icc a b)
          exact hRx.comp hC.continuousOn hM
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
          (f := fun x => fluxX F G x y) (f' := fun x => rateX F G x y) ?_ hline.intervalIntegrable]
        · simp only [fluxX, hx y hy', sub_self]
        · intro x hx'
          rw [uIcc_of_le hab] at hx'
          exact fluxX_deriv F G x y (dFx x hx' y hy') (dGx x hx' y hy')
      _ = 0 := intervalIntegral.integral_zero
  have intY : box a b c d (rateY F G).uncurry = 0 := by
    rw [box_columns hab hcd hRy]
    calc
      (∫ x in a..b, ∫ y in c..d, rateY F G x y) = ∫ _ in a..b, (0 : ℂ) := by
        apply intervalIntegral.integral_congr
        intro x hx'
        rw [uIcc_of_le hab] at hx'
        have hline : ContinuousOn (rateY F G x) (uIcc c d) := by
          rw [uIcc_of_le hcd]
          let line : ℝ → ℝ × ℝ := fun t => (x, t)
          have hC : Continuous line :=
            (continuous_const : Continuous (fun _ : ℝ => x)).prodMk continuous_id
          have hM : MapsTo line (Icc c d) (rectangle a b c d) :=
            fun _ ht => ⟨hx', ht⟩
          change ContinuousOn ((rateY F G).uncurry ∘ line) (Icc c d)
          exact hRy.comp hC.continuousOn hM
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
          (f := fluxY F G x) (f' := rateY F G x) ?_ hline.intervalIntegrable]
        · apply sub_eq_zero.mpr
          simpa [fluxY, div_eq_mul_inv, mul_neg] using congrArg Neg.neg (hy x hx')
        · intro y hy'
          rw [uIcc_of_le hcd] at hy'
          exact fluxY_deriv F G x y (y_ne (x, y) ⟨hx', hy'⟩)
            (dFy x hx' y hy') (dGy x hx' y hy')
      _ = 0 := intervalIntegral.integral_zero
  apply sub_eq_zero.mp
  calc
    box a b c d (density F (adjointExpression G)) -
        box a b c d (density (raising F) G) =
      box a b c d (fun z => density F (adjointExpression G) z -
        density (raising F) G z) := by
          exact (integral_sub (continuous_integrable hL) (continuous_integrable hR)).symm
    _ = box a b c d (fun z => rateX F G z.1 z.2 + rateY F G z.1 z.2) :=
      box_congr (fun z hz => density_difference F G z.1 z.2 (y_ne z hz))
    _ = 0 := by rw [box_add hRx hRy, intX, intY, add_zero]

end
end ManuscriptAudit.Paper8MaassRectangleAdjoint

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8MaassRectangleAdjoint.green_identity
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
