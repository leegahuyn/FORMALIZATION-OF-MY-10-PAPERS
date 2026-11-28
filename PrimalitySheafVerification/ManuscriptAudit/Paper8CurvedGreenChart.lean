import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.MaassLaplacian

/-! Pullback of a complex current under a variable-lower-bound rectangle chart. -/

namespace ManuscriptAudit.Paper8CurvedGreenChart

open Function MaassLaplacian

noncomputable section

def height (lower : ℝ → ℝ) (Y x t : ℝ) : ℝ :=
  lower x + t * (Y - lower x)

def point (lower : ℝ → ℝ) (Y x t : ℝ) : ℂ :=
  complexPoint x (height lower Y x t)

def slope (lower : ℝ → ℝ) (x t : ℝ) : ℝ := (1 - t) * deriv lower x

def pullbackX (J : ℂ → ℂ) (lower : ℝ → ℝ) (Y x t : ℝ) : ℂ :=
  (1 + Complex.I * (slope lower x t : ℂ)) * J (point lower Y x t)

def pullbackT (J : ℂ → ℂ) (lower : ℝ → ℝ) (Y x t : ℝ) : ℂ :=
  Complex.I * ((Y - lower x : ℝ) : ℂ) * J (point lower Y x t)

def rateX (J : ℂ → ℂ) (lower : ℝ → ℝ) (Y x t : ℝ) : ℂ :=
  -Complex.I * ((deriv lower x : ℝ) : ℂ) * J (point lower Y x t) +
    Complex.I * ((Y - lower x : ℝ) : ℂ) *
      (fderiv ℝ J (point lower Y x t) 1 +
        (slope lower x t : ℂ) * fderiv ℝ J (point lower Y x t) Complex.I)

def rateT (J : ℂ → ℂ) (lower : ℝ → ℝ) (Y x t : ℝ) : ℂ :=
  -Complex.I * ((deriv lower x : ℝ) : ℂ) * J (point lower Y x t) +
    (1 + Complex.I * (slope lower x t : ℂ)) *
      (((Y - lower x : ℝ) : ℂ) * fderiv ℝ J (point lower Y x t) Complex.I)

private theorem height_hasDerivAt_x {lower : ℝ → ℝ} {Y x t : ℝ}
    (hLower : DifferentiableAt ℝ lower x) :
    HasDerivAt (fun u => height lower Y u t) (slope lower x t) x := by
  have h := hLower.hasDerivAt.add ((hLower.hasDerivAt.const_sub Y).const_mul t)
  have hD : deriv lower x + t * (-deriv lower x) = slope lower x t := by
    unfold slope
    ring
  have hFun : (fun u => height lower Y u t) = lower + (fun u => t * (Y - lower u)) := by
    funext u
    rfl
  rw [hFun, ← hD]
  exact h

private theorem height_hasDerivAt_t (lower : ℝ → ℝ) (Y x t : ℝ) :
    HasDerivAt (height lower Y x) (Y - lower x) t := by
  change HasDerivAt (fun u : ℝ => lower x + u * (Y - lower x)) (Y - lower x) t
  simpa only [id_eq, one_mul] using
    ((hasDerivAt_id t).mul_const (Y - lower x)).const_add (lower x)

private theorem point_hasDerivAt_x {lower : ℝ → ℝ} {Y x t : ℝ}
    (hLower : DifferentiableAt ℝ lower x) :
    HasDerivAt (fun u => point lower Y u t) (1 + (slope lower x t : ℂ) * Complex.I) x := by
  have hCo : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 x := by
    simpa only [id_eq, Complex.ofReal_one] using (hasDerivAt_id x).ofReal_comp
  exact hCo.add ((height_hasDerivAt_x hLower).ofReal_comp.mul_const Complex.I)

private theorem point_hasDerivAt_t (lower : ℝ → ℝ) (Y x t : ℝ) :
    HasDerivAt (point lower Y x) (((Y - lower x : ℝ) : ℂ) * Complex.I) t :=
  ((height_hasDerivAt_t lower Y x t).ofReal_comp.mul_const Complex.I).const_add (x : ℂ)

theorem pullbackT_hasDerivAt_x {J : ℂ → ℂ} {lower : ℝ → ℝ} {Y x t : ℝ}
    (hLower : DifferentiableAt ℝ lower x) (hJ : DifferentiableAt ℝ J (point lower Y x t)) :
    HasDerivAt (fun u => pullbackT J lower Y u t) (rateX J lower Y x t) x := by
  have hFactor : HasDerivAt (fun u : ℝ => Complex.I * ((Y - lower u : ℝ) : ℂ))
      (-Complex.I * ((deriv lower x : ℝ) : ℂ)) x := by
    simpa only [Complex.ofReal_neg, mul_neg, neg_mul] using
      ((hLower.hasDerivAt.const_sub Y).ofReal_comp).const_mul Complex.I
  have hJComp := hJ.hasFDerivAt.comp_hasDerivAt x (point_hasDerivAt_x hLower)
  let L := fderiv ℝ J (point lower Y x t)
  have hL : L (1 + (slope lower x t : ℂ) * Complex.I) =
      L 1 + (slope lower x t : ℂ) * L Complex.I := by
    change L (1 + slope lower x t • Complex.I) = L 1 + slope lower x t • L Complex.I
    rw [map_add, map_smul]
  change HasDerivAt (J ∘ (fun u => point lower Y u t))
    (L (1 + (slope lower x t : ℂ) * Complex.I)) x at hJComp
  rw [hL] at hJComp
  have hFun : (fun u => pullbackT J lower Y u t) =
      (fun u : ℝ => Complex.I * ((Y - lower u : ℝ) : ℂ)) *
        (J ∘ (fun u => point lower Y u t)) := by
    funext u
    rfl
  rw [hFun]
  exact hFactor.mul hJComp

theorem pullbackX_hasDerivAt_t {J : ℂ → ℂ} {lower : ℝ → ℝ} {Y x t : ℝ}
    (hJ : DifferentiableAt ℝ J (point lower Y x t)) :
    HasDerivAt (pullbackX J lower Y x) (rateT J lower Y x t) t := by
  have hFactor : HasDerivAt (fun u : ℝ => (1 : ℂ) + Complex.I * (slope lower x u : ℂ))
      (-Complex.I * ((deriv lower x : ℝ) : ℂ)) t := by
    have h := (((((hasDerivAt_id t).const_sub 1).mul_const (deriv lower x)).ofReal_comp).const_mul
      Complex.I).const_add 1
    simpa only [slope, id_eq, neg_one_mul, Complex.ofReal_neg, mul_neg, neg_mul] using h
  have hJComp := hJ.hasFDerivAt.comp_hasDerivAt t (point_hasDerivAt_t lower Y x t)
  let L := fderiv ℝ J (point lower Y x t)
  have hL : L (((Y - lower x : ℝ) : ℂ) * Complex.I) =
      ((Y - lower x : ℝ) : ℂ) * L Complex.I := by
    change L ((Y - lower x) • Complex.I) = (Y - lower x) • L Complex.I
    rw [map_smul]
  change HasDerivAt (J ∘ point lower Y x) (L (((Y - lower x : ℝ) : ℂ) * Complex.I)) t at hJComp
  rw [hL] at hJComp
  have hFun : pullbackX J lower Y x =
      (fun u : ℝ => (1 : ℂ) + Complex.I * (slope lower x u : ℂ)) * (J ∘ point lower Y x) := by
    funext u
    rfl
  rw [hFun]
  exact hFactor.mul hJComp

theorem rates_sub (J : ℂ → ℂ) (lower : ℝ → ℝ) (Y x t : ℝ) :
    rateX J lower Y x t - rateT J lower Y x t =
      ((Y - lower x : ℝ) : ℂ) *
        (Complex.I * fderiv ℝ J (point lower Y x t) 1 - fderiv ℝ J (point lower Y x t) Complex.I) := by
  unfold rateX rateT
  ring

end
end ManuscriptAudit.Paper8CurvedGreenChart

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8CurvedGreenChart.pullbackT_hasDerivAt_x,
      ``ManuscriptAudit.Paper8CurvedGreenChart.pullbackX_hasDerivAt_t,
      ``ManuscriptAudit.Paper8CurvedGreenChart.rates_sub] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
