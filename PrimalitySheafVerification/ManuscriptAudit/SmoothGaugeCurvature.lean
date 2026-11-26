import Lean.Util.CollectAxioms
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NoncommRing

/-!
# Ordinary curvature under the affine gauge action

Paper 10, physical PDF pp. 463–464, equations (2.6) and (2.8).
The two components of a connection are its coefficients of `dx` and `dy`.
The gauge and its pointwise inverse are functions into a real normed algebra.
The proof uses the one-variable derivatives of the coordinate slices and
symmetry of the second Fréchet derivative for a twice continuously
differentiable gauge.
-/

namespace ManuscriptAudit.SmoothGaugeCurvature

noncomputable section

abbrev Field2 (A : Type*) := ℝ → ℝ → A

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

def partialX (f : Field2 A) (x y : ℝ) : A :=
  deriv (fun t => f t y) x

def partialY (f : Field2 A) (x y : ℝ) : A :=
  deriv (f x) y

def curvature (ax ay : Field2 A) (x y : ℝ) : A :=
  partialX ay x y - partialY ax x y + ax x y * ay x y - ay x y * ax x y

def affineComponent (g inverse a dg : Field2 A) : Field2 A :=
  fun x y => inverse x y * a x y * g x y + inverse x y * dg x y

private theorem derivativeInverse {g inverse : ℝ → A} {u v : A} {t : ℝ}
    (dg : HasDerivAt g u t) (di : HasDerivAt inverse v t)
    (inverse_mul : ∀ s, inverse s * g s = 1) (mul_inverse : g t * inverse t = 1) :
    v = -(inverse t * u * inverse t) := by
  have hconst : inverse * g = fun _ : ℝ => (1 : A) := funext inverse_mul
  have hd := di.mul dg
  rw [hconst] at hd
  have hz : v * g t + inverse t * u = 0 := hd.unique (hasDerivAt_const t (1 : A))
  have hz' := congrArg (fun a : A => a * inverse t) hz
  rw [add_mul, mul_assoc v, mul_inverse, mul_one, zero_mul] at hz'
  calc
    v = (v + inverse t * u * inverse t) - (inverse t * u * inverse t) := by abel
    _ = -(inverse t * u * inverse t) := by rw [hz', zero_sub]

private theorem derivativeAffineComponent {g inverse a dg : ℝ → A}
    {g' inverse' a' dg' : A} {t : ℝ}
    (di : HasDerivAt inverse inverse' t) (da : HasDerivAt a a' t)
    (d : HasDerivAt g g' t) (dd : HasDerivAt dg dg' t) :
    deriv (fun s => inverse s * a s * g s + inverse s * dg s) t =
      ((inverse' * a t + inverse t * a') * g t + (inverse t * a t) * g') +
        (inverse' * dg t + inverse t * dg') :=
  (((di.mul da).mul d).add (di.mul dd)).deriv

private theorem curvatureAlgebra {R : Type*} [Ring R]
    (g inverse ax ay gx gy ayx axy gxy : R) (mul_inverse : g * inverse = 1) :
    (((-(inverse * gx * inverse) * ay + inverse * ayx) * g + (inverse * ay) * gx) +
        (-(inverse * gx * inverse) * gy + inverse * gxy)) -
      (((-(inverse * gy * inverse) * ax + inverse * axy) * g + (inverse * ax) * gy) +
        (-(inverse * gy * inverse) * gx + inverse * gxy)) +
      (inverse * ax * g + inverse * gx) * (inverse * ay * g + inverse * gy) -
      (inverse * ay * g + inverse * gy) * (inverse * ax * g + inverse * gx) =
      inverse * (ayx - axy + ax * ay - ay * ax) * g := by
  have cancel (a : R) : g * (inverse * a) = a := by
    rw [← mul_assoc, mul_inverse, one_mul]
  noncomm_ring [cancel]

theorem curvature_affine_covariance_at
    (g inverse ax ay : Field2 A) (x y : ℝ)
    (inverse_mul : ∀ s t, inverse s t * g s t = 1)
    (mul_inverse : ∀ s t, g s t * inverse s t = 1)
    (hgx : DifferentiableAt ℝ (fun t => g t y) x)
    (hgy : DifferentiableAt ℝ (g x) y)
    (hix : DifferentiableAt ℝ (fun t => inverse t y) x)
    (hiy : DifferentiableAt ℝ (inverse x) y)
    (hayx : DifferentiableAt ℝ (fun t => ay t y) x)
    (haxy : DifferentiableAt ℝ (ax x) y)
    (hgxy : DifferentiableAt ℝ (fun t => partialY g t y) x)
    (hgyx : DifferentiableAt ℝ (partialX g x) y)
    (hmixed : partialX (partialY g) x y = partialY (partialX g) x y) :
    curvature (affineComponent g inverse ax (partialX g))
      (affineComponent g inverse ay (partialY g)) x y =
      inverse x y * curvature ax ay x y * g x y := by
  have dix : HasDerivAt (fun t => inverse t y)
      (-(inverse x y * partialX g x y * inverse x y)) x := by
    have h := derivativeInverse hgx.hasDerivAt hix.hasDerivAt
      (fun t => inverse_mul t y) (mul_inverse x y)
    exact hix.hasDerivAt.congr_deriv h
  have diy : HasDerivAt (inverse x)
      (-(inverse x y * partialY g x y * inverse x y)) y := by
    have h := derivativeInverse hgy.hasDerivAt hiy.hasDerivAt
      (inverse_mul x) (mul_inverse x y)
    exact hiy.hasDerivAt.congr_deriv h
  have dax : partialX (affineComponent g inverse ay (partialY g)) x y =
      (((-(inverse x y * partialX g x y * inverse x y) * ay x y +
          inverse x y * partialX ay x y) * g x y +
        (inverse x y * ay x y) * partialX g x y) +
        (-(inverse x y * partialX g x y * inverse x y) * partialY g x y +
          inverse x y * partialX (partialY g) x y)) :=
    derivativeAffineComponent dix hayx.hasDerivAt hgx.hasDerivAt hgxy.hasDerivAt
  have day : partialY (affineComponent g inverse ax (partialX g)) x y =
      (((-(inverse x y * partialY g x y * inverse x y) * ax x y +
          inverse x y * partialY ax x y) * g x y +
        (inverse x y * ax x y) * partialY g x y) +
        (-(inverse x y * partialY g x y * inverse x y) * partialX g x y +
          inverse x y * partialY (partialX g) x y)) :=
    derivativeAffineComponent diy haxy.hasDerivAt hgy.hasDerivAt hgyx.hasDerivAt
  unfold curvature
  rw [dax, day, ← hmixed]
  exact curvatureAlgebra (g x y) (inverse x y) (ax x y) (ay x y)
    (partialX g x y) (partialY g x y) (partialX ay x y) (partialY ax x y)
    (partialX (partialY g) x y) (mul_inverse x y)


private theorem hasDerivAtSliceX (f : Field2 A) (x y : ℝ)
    (hf : DifferentiableAt ℝ (Function.uncurry f) (x, y)) :
    HasDerivAt (fun t => f t y) (fderiv ℝ (Function.uncurry f) (x, y) (1, 0)) x := by
  have h := hf.hasFDerivAt.comp_hasDerivAt x ((hasDerivAt_id' x).prodMk (hasDerivAt_const x y))
  exact h

private theorem hasDerivAtSliceY (f : Field2 A) (x y : ℝ)
    (hf : DifferentiableAt ℝ (Function.uncurry f) (x, y)) :
    HasDerivAt (f x) (fderiv ℝ (Function.uncurry f) (x, y) (0, 1)) y :=
  hf.hasFDerivAt.comp_hasDerivAt y ((hasDerivAt_const y x).prodMk (hasDerivAt_id' y))

private theorem hasFDerivAtEvalFDeriv (g : Field2 A) (p v : ℝ × ℝ)
    (hg : DifferentiableAt ℝ (fderiv ℝ (Function.uncurry g)) p) :
    HasFDerivAt (fun q => fderiv ℝ (Function.uncurry g) q v)
      ((ContinuousLinearMap.apply ℝ A v).comp
        (fderiv ℝ (fderiv ℝ (Function.uncurry g)) p)) p :=
  (ContinuousLinearMap.apply ℝ A v).hasFDerivAt.comp p hg.hasFDerivAt

private theorem mixedDerivsOfContDiff (g : Field2 A) (x y : ℝ)
    (hg : ContDiff ℝ 2 (Function.uncurry g)) :
    ∃ d : A, HasDerivAt (fun t => partialY g t y) d x ∧
      HasDerivAt (partialX g x) d y := by
  have hd := hg.differentiable (by simp)
  have hdd := (hg.fderiv_right (m := 1) (by decide)).differentiable_one
  have hx : HasDerivAt (fun t => partialY g t y)
      (fderiv ℝ (fderiv ℝ (Function.uncurry g)) (x, y) (1, 0) (0, 1)) x := by
    have heq : (fun t => partialY g t y) =
        fun t => fderiv ℝ (Function.uncurry g) (t, y) (0, 1) :=
      funext fun t => (hasDerivAtSliceY g t y (hd (t, y))).deriv
    rw [heq]
    exact (hasFDerivAtEvalFDeriv g (x, y) (0, 1) (hdd (x, y))).comp_hasDerivAt x
      ((hasDerivAt_id' x).prodMk (hasDerivAt_const x y))
  have hy : HasDerivAt (partialX g x)
      (fderiv ℝ (fderiv ℝ (Function.uncurry g)) (x, y) (0, 1) (1, 0)) y := by
    have heq : partialX g x =
        fun t => fderiv ℝ (Function.uncurry g) (x, t) (1, 0) :=
      funext fun t => (hasDerivAtSliceX g x t (hd (x, t))).deriv
    rw [heq]
    exact (hasFDerivAtEvalFDeriv g (x, y) (1, 0) (hdd (x, y))).comp_hasDerivAt y
      ((hasDerivAt_const y x).prodMk (hasDerivAt_id' y))
  have hsymm : IsSymmSndFDerivAt ℝ (Function.uncurry g) (x, y) :=
    hg.contDiffAt.isSymmSndFDerivAt (by simp)
  refine ⟨_, hx, ?_⟩
  rw [hsymm.eq (1, 0) (0, 1)]
  exact hy

/-- A twice continuously differentiable gauge and a continuously differentiable inverse
give ordinary curvature covariance for a continuously differentiable connection. -/
theorem curvature_affine_covariance
    (g inverse ax ay : Field2 A) (x y : ℝ)
    (inverse_mul : ∀ s t, inverse s t * g s t = 1)
    (mul_inverse : ∀ s t, g s t * inverse s t = 1)
    (hg : ContDiff ℝ 2 (Function.uncurry g))
    (hi : ContDiff ℝ 1 (Function.uncurry inverse))
    (hax : ContDiff ℝ 1 (Function.uncurry ax))
    (hay : ContDiff ℝ 1 (Function.uncurry ay)) :
    curvature (affineComponent g inverse ax (partialX g))
      (affineComponent g inverse ay (partialY g)) x y =
      inverse x y * curvature ax ay x y * g x y := by
  have hg' := hg.differentiable (by simp) (x, y)
  have hi' := hi.differentiable_one (x, y)
  obtain ⟨_, hxy, hyx⟩ := mixedDerivsOfContDiff g x y hg
  exact curvature_affine_covariance_at g inverse ax ay x y inverse_mul mul_inverse
    (hasDerivAtSliceX g x y hg').differentiableAt
    (hasDerivAtSliceY g x y hg').differentiableAt
    (hasDerivAtSliceX inverse x y hi').differentiableAt
    (hasDerivAtSliceY inverse x y hi').differentiableAt
    (hasDerivAtSliceX ay x y (hay.differentiable_one (x, y))).differentiableAt
    (hasDerivAtSliceY ax x y (hax.differentiable_one (x, y))).differentiableAt
    hxy.differentiableAt hyx.differentiableAt (hxy.deriv.trans hyx.deriv.symm)

end

end ManuscriptAudit.SmoothGaugeCurvature

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.SmoothGaugeCurvature.curvature_affine_covariance_at,
      ``ManuscriptAudit.SmoothGaugeCurvature.curvature_affine_covariance] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
