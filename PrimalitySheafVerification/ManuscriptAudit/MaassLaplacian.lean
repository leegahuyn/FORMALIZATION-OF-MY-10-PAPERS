import Lean.Util.CollectAxioms
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Paper 9, physical PDF p. 409. This computes the displayed differential
expression Δ for a holomorphic function multiplied by a real power of y.
The result concerns pointwise derivatives on the upper half plane.
-/

namespace ManuscriptAudit.MaassLaplacian

open Filter Set

open scoped Topology

noncomputable section

def complexPoint (x y : ℝ) : ℂ :=
  (x : ℂ) + (y : ℂ) * Complex.I

private def heightPower (a y : ℝ) : ℂ :=
  ((y ^ a : ℝ) : ℂ)

/-- The function obtained by multiplying a holomorphic function by y to the power a. -/
def weighted (a : ℝ) (f : ℂ → ℂ) (x y : ℝ) : ℂ :=
  heightPower a y * f (complexPoint x y)

def partialX (F : ℝ → ℝ → ℂ) (x y : ℝ) : ℂ :=
  deriv (fun t => F t y) x

def partialY (F : ℝ → ℝ → ℂ) (x y : ℝ) : ℂ :=
  deriv (fun t => F x t) y

/-- The pointwise expression printed as Δ_k. -/
def maassDelta (k : ℝ) (F : ℝ → ℝ → ℂ) (x y : ℝ) : ℂ :=
  -((y : ℂ) ^ 2) * (partialX (partialX F) x y + partialY (partialY F) x y) +
    Complex.I * (k : ℂ) * (y : ℂ) * partialX F x y

@[simp] theorem complexPoint_im (x y : ℝ) : (complexPoint x y).im = y := by
  simp [complexPoint, Complex.add_im, Complex.mul_im]

private theorem ofReal_derivative (r : ℝ) :
    HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) r := by
  simpa only [Complex.ofReal_one] using (hasDerivAt_id r).ofReal_comp

private theorem horizontal_derivative {f : ℂ → ℂ} {x y : ℝ} {d : ℂ}
    (h : HasDerivAt f d (complexPoint x y)) :
    HasDerivAt (fun t => f (complexPoint t y)) d x := by
  have hl : HasDerivAt (fun t => complexPoint t y) (1 : ℂ) x :=
    (ofReal_derivative x).add_const ((y : ℂ) * Complex.I)
  simpa only [Function.comp_apply, one_smul] using h.scomp x hl

private theorem vertical_derivative {f : ℂ → ℂ} {x y : ℝ} {d : ℂ}
    (h : HasDerivAt f d (complexPoint x y)) :
    HasDerivAt (fun t => f (complexPoint x t)) (Complex.I * d) y := by
  have hl : HasDerivAt (fun t => complexPoint x t) Complex.I y := by
    simpa only [complexPoint, one_mul] using
      ((ofReal_derivative y).mul_const Complex.I).const_add (x : ℂ)
  simpa only [Function.comp_apply, smul_eq_mul] using h.scomp y hl

private theorem heightPower_derivative (a : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (heightPower a) ((a : ℂ) * heightPower (a - 1) y) y := by
  simpa only [heightPower, Complex.ofReal_mul] using
    (Real.hasDerivAt_rpow_const (p := a) (Or.inl hy.ne')).ofReal_comp

private theorem shiftHeight_one (a : ℝ) {y : ℝ} (hy : 0 < y) :
    (y : ℂ) * heightPower (a - 1) y = heightPower a y := by
  have h := Real.rpow_add hy 1 (a - 1)
  rw [show (1 : ℝ) + (a - 1) = a by ring, Real.rpow_one] at h
  simpa only [heightPower, Complex.ofReal_mul] using congrArg Complex.ofReal h.symm

private theorem shiftHeight_two (a : ℝ) {y : ℝ} (hy : 0 < y) :
    (y : ℂ) ^ 2 * heightPower (a - 2) y = heightPower a y := by
  have h := Real.rpow_add hy 2 (a - 2)
  rw [show (2 : ℝ) + (a - 2) = a by ring, Real.rpow_natCast y 2] at h
  simpa only [heightPower, Complex.ofReal_mul, Complex.ofReal_pow] using
    congrArg Complex.ofReal h.symm

set_option maxHeartbeats 600000 in
/-- A holomorphic function multiplied by y to the power a solves the
weight-2a differential equation with eigenvalue a(1-a). -/
theorem delta_weighted (f : ℂ → ℂ) (a x y : ℝ) (hy : 0 < y)
    (hf : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ f z) :
    maassDelta (2 * a) (weighted a f) x y =
      (a : ℂ) * (1 - (a : ℂ)) * weighted a f x y := by
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hOn : DifferentiableOn ℂ f {z : ℂ | 0 < z.im} := fun z hz => (hf z hz).differentiableWithinAt
  have hf' (z : ℂ) (hz : 0 < z.im) : DifferentiableAt ℂ (deriv f) z :=
    (hOn.deriv hopen z hz).differentiableAt (hopen.mem_nhds hz)
  have hx (t : ℝ) : partialX (weighted a f) t y =
      heightPower a y * deriv f (complexPoint t y) :=
    (HasDerivAt.const_mul (heightPower a y)
      (horizontal_derivative (hf (complexPoint t y) (by simpa only [complexPoint_im] using hy)).hasDerivAt)).deriv
  have hxx : partialX (partialX (weighted a f)) x y =
      heightPower a y * deriv (deriv f) (complexPoint x y) := by
    change deriv (fun t => partialX (weighted a f) t y) x = _
    rw [funext hx]
    exact (HasDerivAt.const_mul (heightPower a y)
      (horizontal_derivative (hf' (complexPoint x y) (by simpa only [complexPoint_im] using hy)).hasDerivAt)).deriv
  let e : ℝ → ℂ := fun t =>
    (a : ℂ) * heightPower (a - 1) t * f (complexPoint x t) +
      heightPower a t * (Complex.I * deriv f (complexPoint x t))
  have eh : (fun t => partialY (weighted a f) x t) =ᶠ[𝓝 y] e := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact ((heightPower_derivative a ht).mul
      (vertical_derivative (hf (complexPoint x t) (by simpa only [complexPoint_im] using ht)).hasDerivAt)).deriv
  have hd : HasDerivAt (fun t => (a : ℂ) * heightPower (a - 1) t)
      ((a : ℂ) * ((a - 1 : ℝ) : ℂ) * heightPower (a - 2) y) y := by
    simpa only [show a - 1 - 1 = a - 2 by ring, mul_assoc] using
      HasDerivAt.const_mul (a : ℂ) (heightPower_derivative (a - 1) hy)
  have hyy : partialY (partialY (weighted a f)) x y =
      (a : ℂ) * ((a - 1 : ℝ) : ℂ) * heightPower (a - 2) y * f (complexPoint x y) +
      ((a : ℂ) * heightPower (a - 1) y) * (Complex.I * deriv f (complexPoint x y)) +
      ((a : ℂ) * heightPower (a - 1) y * (Complex.I * deriv f (complexPoint x y)) +
        heightPower a y * (Complex.I * (Complex.I * deriv (deriv f) (complexPoint x y)))) := by
    change deriv (fun t => partialY (weighted a f) x t) y = _
    have ht : 0 < (complexPoint x y).im := by simpa only [complexPoint_im] using hy
    have h1 := hd.mul (vertical_derivative (hf _ ht).hasDerivAt)
    have h2 := (heightPower_derivative a hy).mul
      (HasDerivAt.const_mul Complex.I (vertical_derivative (hf' _ ht).hasDerivAt))
    exact eh.deriv_eq.trans (h1.add h2).deriv
  have hshift : (y : ℂ) ^ 2 * heightPower (a - 1) y = (y : ℂ) * heightPower a y := by
    rw [pow_two, mul_assoc, shiftHeight_one a hy]
  have hi (w : ℂ) : Complex.I * (Complex.I * w) = -w := by
    rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
  rw [maassDelta, hxx, hyy, hx, hi]
  calc
    _ = -(a : ℂ) * ((a - 1 : ℝ) : ℂ) *
          ((y : ℂ) ^ 2 * heightPower (a - 2) y) * f (complexPoint x y) -
        2 * (a : ℂ) * Complex.I * ((y : ℂ) ^ 2 * heightPower (a - 1) y) *
          deriv f (complexPoint x y) +
        Complex.I * ((2 * a : ℝ) : ℂ) * ((y : ℂ) * heightPower a y) *
          deriv f (complexPoint x y) := by ring
    _ = _ := by
      rw [shiftHeight_two a hy, hshift]
      simp only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_ofNat,
        Complex.ofReal_one, weighted]
      ring

/-- The pointwise differential equation in the paper's weight convention. -/
theorem delta_weighted_halfWeight (f : ℂ → ℂ) (k x y : ℝ) (hy : 0 < y)
    (hf : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ f z) :
    maassDelta k (weighted (k / 2) f) x y =
      ((k / 2 : ℝ) : ℂ) * (1 - ((k / 2 : ℝ) : ℂ)) * weighted (k / 2) f x y := by
  simpa only [show 2 * (k / 2) = k by ring] using delta_weighted f (k / 2) x y hy hf

/-- The actual Mathlib Jacobi theta yields the pointwise weight-1/2
eigenvalue 3/16 after multiplication by y^(1/4). -/
theorem jacobiTheta_delta_half (x y : ℝ) (hy : 0 < y) :
    maassDelta (1 / 2) (weighted (1 / 4) jacobiTheta) x y =
      (3 / 16 : ℂ) * weighted (1 / 4) jacobiTheta x y := by
  have h := delta_weighted jacobiTheta (1 / 4) x y hy
    (fun _ hz => differentiableAt_jacobiTheta hz)
  norm_num [Complex.ofReal_div] at h ⊢
  exact h

end

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``delta_weighted, ``delta_weighted_halfWeight, ``jacobiTheta_delta_half] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"

end ManuscriptAudit.MaassLaplacian
