import Lean.Util.CollectAxioms
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Congr
import PrimalitySheafVerification.ManuscriptAudit.Paper8MaassCriticalHolomorphic
import PrimalitySheafVerification.ManuscriptAudit.Paper8MaassRectangleEnergy

/-! Native Schwarz symmetry supplies all coordinate hypotheses for the weight −1/2 factorization. -/

namespace ManuscriptAudit.Paper8OddMaassSmoothFactorization

open Filter Set UpperHalfPlane MaassLaplacian
open Paper8MaassCriticalHolomorphic Paper8NegativeHalfMaassFactorization
open Paper8MaassRectangleEnergy
open scoped Topology

noncomputable section

private theorem isOpen_upper : IsOpen {w : ℂ | 0 < w.im} :=
  isOpen_lt continuous_const Complex.continuous_im

private theorem at_of_contDiffOn {F : ℂ → ℂ} (hF : ContDiffOn ℝ 2 F {w : ℂ | 0 < w.im})
    {w : ℂ} (hw : 0 < w.im) : ContDiffAt ℝ 2 F w :=
  (hF w hw).contDiffAt (isOpen_upper.mem_nhds hw)

private theorem point_positive {x y : ℝ} (hy : 0 < y) : 0 < (complexPoint x y).im := by
  rwa [complexPoint_im]

private theorem dirPart_fderiv {F : ℂ → ℂ} {w : ℂ}
    (hF : ContDiffAt ℝ 2 F w) (v : ℂ) :
    HasFDerivAt (fun q : ℂ => fderiv ℝ F q v)
      ((ContinuousLinearMap.apply ℝ ℂ v).comp (fderiv ℝ (fderiv ℝ F) w)) w := by
  have hOne : ContDiffAt ℝ 1 (fderiv ℝ F) w := hF.fderiv_right (by norm_num)
  have hD : DifferentiableAt ℝ (fderiv ℝ F) w := hOne.differentiableAt (by norm_num)
  exact (ContinuousLinearMap.apply ℝ ℂ v).hasFDerivAt.comp w hD.hasFDerivAt

private theorem profileDir_eq_partialX {F : ℂ → ℂ} {x y : ℝ}
    (hF : DifferentiableAt ℝ F (complexPoint x y)) :
    partialX (realProfile F) x y = fderiv ℝ F (complexPoint x y) 1 := by
  have hPoint : HasDerivAt (fun t => complexPoint t y) (1 : ℂ) x := by
    simpa only [id_eq] using horizontal_derivative (hasDerivAt_id (complexPoint x y))
  exact (hF.hasFDerivAt.comp_hasDerivAt x hPoint).deriv

private theorem profileDir_eq_partialY {F : ℂ → ℂ} {x y : ℝ}
    (hF : DifferentiableAt ℝ F (complexPoint x y)) :
    partialY (realProfile F) x y = fderiv ℝ F (complexPoint x y) Complex.I := by
  have hPoint : HasDerivAt (fun t => complexPoint x t) Complex.I y := by
    simpa only [id_eq, mul_one] using vertical_derivative (hasDerivAt_id (complexPoint x y))
  exact (hF.hasFDerivAt.comp_hasDerivAt y hPoint).deriv

private theorem second_order_coordinates {F : ℂ → ℂ}
    (hF : ContDiffOn ℝ 2 F {w : ℂ | 0 < w.im}) (x y : ℝ) (hy : 0 < y) :
    DifferentiableAt ℝ (fun t => realProfile F t y) x ∧
    DifferentiableAt ℝ (realProfile F x) y ∧
    DifferentiableAt ℝ (fun t => partialX (realProfile F) t y) x ∧
    DifferentiableAt ℝ (partialX (realProfile F) x) y ∧
    DifferentiableAt ℝ (fun t => partialY (realProfile F) t y) x ∧
    DifferentiableAt ℝ (partialY (realProfile F) x) y ∧
    partialX (partialY (realProfile F)) x y = partialY (partialX (realProfile F)) x y := by
  let w := complexPoint x y
  let Dx (q : ℂ) := fderiv ℝ F q 1
  let Dy (q : ℂ) := fderiv ℝ F q Complex.I
  have hAt : ContDiffAt ℝ 2 F w := at_of_contDiffOn hF (point_positive hy)
  have hd (q : ℂ) (hq : 0 < q.im) : DifferentiableAt ℝ F q :=
    (at_of_contDiffOn hF hq).differentiableAt (by norm_num)
  have hw : DifferentiableAt ℝ F w := hd w (point_positive hy)
  have hDx := dirPart_fderiv hAt (1 : ℂ)
  have hDy := dirPart_fderiv hAt Complex.I
  have hXX : (fun t => partialX (realProfile F) t y) = (fun t => realProfile Dx t y) := by
    funext t
    exact profileDir_eq_partialX (hd _ (point_positive hy))
  have hYX : (fun t => partialY (realProfile F) t y) = (fun t => realProfile Dy t y) := by
    funext t
    exact profileDir_eq_partialY (hd _ (point_positive hy))
  have hXY : (partialX (realProfile F) x) =ᶠ[𝓝 y] (realProfile Dx x) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact profileDir_eq_partialX (hd _ (point_positive ht))
  have hYY : (partialY (realProfile F) x) =ᶠ[𝓝 y] (realProfile Dy x) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact profileDir_eq_partialY (hd _ (point_positive ht))
  refine ⟨(profile_horizontal hw).differentiableAt, (profile_vertical hw).differentiableAt,
    hXX.symm ▸ (profile_horizontal hDx.differentiableAt).differentiableAt,
    hXY.differentiableAt_iff.2 (profile_vertical hDx.differentiableAt).differentiableAt,
    hYX.symm ▸ (profile_horizontal hDy.differentiableAt).differentiableAt,
    hYY.differentiableAt_iff.2 (profile_vertical hDy.differentiableAt).differentiableAt, ?_⟩
  change deriv (fun t => partialY (realProfile F) t y) x =
    deriv (partialX (realProfile F) x) y
  rw [hYX, hXY.deriv_eq]
  change partialX (realProfile Dy) x y = partialY (realProfile Dx) x y
  rw [profileDir_eq_partialX hDy.differentiableAt, profileDir_eq_partialY hDx.differentiableAt,
    hDy.fderiv, hDx.fderiv]
  exact hAt.isSymmSndFDerivAt (by simp) 1 Complex.I

def raisedField (F : ℂ → ℂ) (w : ℂ) : ℂ :=
  Complex.I * (w.im : ℂ) * fderiv ℝ F w 1 +
    (w.im : ℂ) * fderiv ℝ F w Complex.I - (1 / 4 : ℂ) * F w

theorem raisedField_realProfile {F : ℂ → ℂ} (hF : ContDiffOn ℝ 2 F {w : ℂ | 0 < w.im})
    (x y : ℝ) (hy : 0 < y) : raisedField F (complexPoint x y) = raising (realProfile F) x y := by
  have h := (at_of_contDiffOn hF (point_positive (x := x) hy)).differentiableAt (by norm_num)
  simp only [raisedField, raising, profileDir_eq_partialX h, profileDir_eq_partialY h,
    complexPoint_im, realProfile]

theorem raisedField_differentiableAt {F : ℂ → ℂ} (hF : ContDiffOn ℝ 2 F {w : ℂ | 0 < w.im})
    (w : ℂ) (hw : 0 < w.im) : DifferentiableAt ℝ (raisedField F) w := by
  have hAt := at_of_contDiffOn hF hw
  have hH : DifferentiableAt ℝ (fun q : ℂ => (q.im : ℂ)) w :=
    Complex.ofRealCLM.differentiableAt.comp w Complex.imCLM.differentiableAt
  have hX := (dirPart_fderiv hAt (1 : ℂ)).differentiableAt
  have hY := (dirPart_fderiv hAt Complex.I).differentiableAt
  have hP : DifferentiableAt ℝ F w := hAt.differentiableAt (by norm_num)
  exact ((((differentiableAt_const _).mul hH).mul hX).add (hH.mul hY)).sub
    ((differentiableAt_const _).mul hP)

theorem raisedField_contDiffOn {F : ℂ → ℂ} (hF : ContDiffOn ℝ 2 F {w : ℂ | 0 < w.im}) :
    ContDiffOn ℝ 1 (raisedField F) {w : ℂ | 0 < w.im} := by
  let U : Set ℂ := {w : ℂ | 0 < w.im}
  have hL : ContDiffOn ℝ 1 (fderiv ℝ F) U :=
    ((contDiffOn_succ_iff_fderiv_of_isOpen (n := 1) isOpen_upper).1 hF).2.2
  have hD (v : ℂ) : ContDiffOn ℝ 1 (fun w : ℂ => fderiv ℝ F w v) U := by
    intro w hw
    exact ((ContinuousLinearMap.apply ℝ ℂ v).contDiff.contDiffAt.comp w
      ((hL w hw).contDiffAt (isOpen_upper.mem_nhds hw))).contDiffWithinAt
  have hHeight : ContDiff ℝ 1 (fun w : ℂ => (w.im : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp Complex.imCLM.contDiff
  have hF' : ContDiffOn ℝ 1 F U := hF.of_le (by norm_num)
  unfold raisedField
  exact (((contDiffOn_const.mul hHeight.contDiffOn).mul (hD 1)).add
    (hHeight.contDiffOn.mul (hD Complex.I))).sub (contDiffOn_const.mul hF')

theorem raisedField_adjoint_of_eigenvalue {F : ℂ → ℂ} {eigenvalue : ℝ}
    (hF : ContDiffOn ℝ 2 F {w : ℂ | 0 < w.im})
    (hEigen : ∀ x y : ℝ, 0 < y →
      maassDelta (-1 / 2) (realProfile F) x y = (eigenvalue : ℂ) * realProfile F x y)
    (x y : ℝ) (hy : 0 < y) : adjointExpression (realProfile (raisedField F)) x y =
      ((eigenvalue - 3 / 16 : ℝ) : ℂ) * realProfile F x y := by
  obtain ⟨hx, hy', hxx, hxy, hyx, hyy, hMixed⟩ := second_order_coordinates hF x y hy
  have hSpec := spectral_equation_for_raising (realProfile F) x y eigenvalue
    hx hy' hxx hxy hyx hyy hMixed (hEigen x y hy)
  have hX : (fun t => realProfile (raisedField F) t y) =
      (fun t => raising (realProfile F) t y) := by
    funext t
    exact raisedField_realProfile hF t y hy
  have hY : realProfile (raisedField F) x =ᶠ[𝓝 y] raising (realProfile F) x := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact raisedField_realProfile hF x t ht
  have hPX : partialX (realProfile (raisedField F)) x y =
      partialX (raising (realProfile F)) x y := by
    unfold partialX
    rw [hX]
  have hPY : partialY (realProfile (raisedField F)) x y =
      partialY (raising (realProfile F)) x y := by
    unfold partialY
    exact hY.deriv_eq
  unfold adjointExpression
  rw [hPX, hPY, show realProfile (raisedField F) x y = raising (realProfile F) x y from
    raisedField_realProfile hF x y hy]
  change adjointExpression (raising (realProfile F)) x y = _
  exact hSpec

theorem critical_raisedField_adjoint {F : ℂ → ℂ}
    (hF : ContDiffOn ℝ 2 F {w : ℂ | 0 < w.im})
    (hEigen : ∀ x y : ℝ, 0 < y →
      maassDelta (-1 / 2) (realProfile F) x y = (3 / 16 : ℂ) * realProfile F x y)
    (x y : ℝ) (hy : 0 < y) : adjointExpression (realProfile (raisedField F)) x y = 0 := by
  have hP (u v : ℝ) (hv : 0 < v) : maassDelta (-1 / 2) (realProfile F) u v =
      (((3 / 16 : ℝ) : ℂ)) * realProfile F u v := by
    push_cast
    exact hEigen u v hv
  simpa only [sub_self, Complex.ofReal_zero, zero_mul] using raisedField_adjoint_of_eigenvalue hF hP x y hy

end
end ManuscriptAudit.Paper8OddMaassSmoothFactorization

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8OddMaassSmoothFactorization.critical_raisedField_adjoint
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
