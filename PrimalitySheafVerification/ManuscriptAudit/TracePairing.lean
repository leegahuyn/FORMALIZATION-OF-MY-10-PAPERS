import Lean.Util.CollectAxioms
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The printed complex trace pairing

Paper 10, pp. 466 and 489, pairs two complex forms by applying a
linear trace to their product. Multiplication of those forms is complex
bilinear. A complex bilinear pairing vanishes if it also has a
conjugate-linear slot.
-/

namespace ManuscriptAudit.TracePairing

private theorem eq_zero_of_I_mul_eq_neg {z : ℂ}
    (h : Complex.I * z = -(Complex.I * z)) : z = 0 := by
  have hz : Complex.I * z + Complex.I * z = 0 :=
    (congrArg (fun w => w + Complex.I * z) h).trans (neg_add_cancel _)
  rw [← two_mul, ← mul_assoc] at hz
  exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero two_ne_zero Complex.I_ne_zero)

theorem paper10_sesquilinear_bilinear_pair_eq_zero {U V : Type*}
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    (B : U →ₗ[ℂ] V →ₗ[ℂ] ℂ)
    (hs : (∀ (c : ℂ) (x : U) (y : V), B x (c • y) = star c * B x y) ∨
          (∀ (c : ℂ) (x : U) (y : V), B (c • x) y = star c * B x y)) :
    B = 0 := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change B x y = 0
  have h (c : ℂ) : c * B x y = star c * B x y := by
    rcases hs with hr | hl
    · simpa only [map_smul, smul_eq_mul] using hr c x y
    · simpa only [map_smul, LinearMap.smul_apply, smul_eq_mul] using hl c x y
  have hi : Complex.I * B x y = -(Complex.I * B x y) := by
    simpa only [Complex.star_def, Complex.conj_I, neg_mul] using h Complex.I
  exact eq_zero_of_I_mul_eq_neg hi

/-- In either sesquilinear convention, a complex-bilinear family cannot
act skew-adjointly in all complex directions unless every action is
invisible to the pairing. -/
theorem paper10_complex_skew_family_pair_eq_zero {U : Type*}
    [AddCommGroup U] [Module ℂ U]
    (B : U →ₗ[ℂ] U →ₗ[ℂ] U) (P : U → U → ℂ)
    (hP : (∀ (c : ℂ) x y, P (c • x) y = c * P x y ∧
          P x (c • y) = star c * P x y) ∨
      (∀ (c : ℂ) x y, P (c • x) y = star c * P x y ∧
          P x (c • y) = c * P x y))
    (hSkew : ∀ u v w, P (B u v) w = -P v (B u w)) :
    ∀ u v w, P (B u v) w = 0 := by
  intro u v w
  have hPair : P v (B u w) = -P (B u v) w := by
    rw [hSkew u v w, neg_neg]
  have hB (z : U) : B (Complex.I • u) z = Complex.I • B u z := by
    rw [map_smul, LinearMap.smul_apply]
  have hs := hSkew (Complex.I • u) v w
  rw [hB v, hB w] at hs
  apply eq_zero_of_I_mul_eq_neg
  rcases hP with hP | hP
  · rw [(hP Complex.I (B u v) w).1, (hP Complex.I v (B u w)).2,
      hPair, Complex.star_def, Complex.conj_I, neg_mul_neg] at hs
    exact hs
  · rw [(hP Complex.I (B u v) w).1, (hP Complex.I v (B u w)).2,
      hPair, Complex.star_def, Complex.conj_I, neg_mul, mul_neg, neg_neg] at hs
    exact hs.symm

/-- With a left-nondegenerate pairing, the printed all-direction
skew-adjointness forces the entire complex-bilinear map to vanish. -/
theorem paper10_complex_skew_family_eq_zero {U : Type*}
    [AddCommGroup U] [Module ℂ U]
    (B : U →ₗ[ℂ] U →ₗ[ℂ] U) (P : U → U → ℂ)
    (hP : (∀ (c : ℂ) x y, P (c • x) y = c * P x y ∧
          P x (c • y) = star c * P x y) ∨
      (∀ (c : ℂ) x y, P (c • x) y = star c * P x y ∧
          P x (c • y) = c * P x y))
    (hSkew : ∀ u v w, P (B u v) w = -P v (B u w))
    (hND : ∀ z, (∀ w, P z w = 0) → z = 0) :
    B = 0 := by
  apply LinearMap.ext
  intro u
  apply LinearMap.ext
  intro v
  change B u v = 0
  exact hND (B u v) (paper10_complex_skew_family_pair_eq_zero B P hP hSkew u v)

/-- Equality with the negative conjugate kills the real part. -/
theorem real_part_eq_zero_of_eq_neg_star (z : ℂ) (h : z = -star z) :
    z.re = 0 := by
  have hRe := congrArg Complex.re h
  simp only [Complex.star_def, Complex.neg_re, Complex.conj_re] at hRe
  linarith

/-- The step from skew-adjointness to zero diagonal is false for a
genuine complex sesquilinear pairing. Multiplication by (i) on the
complex line is skew-adjoint and has the nonzero diagonal value (i). -/
theorem paper10_skew_pairing_diagonal_need_not_vanish :
    ∃ (B : ℂ → ℂ → ℂ) (T : ℂ →ₗ[ℂ] ℂ),
      (∀ c x y : ℂ, B (c • x) y = c * B x y ∧
        B x (c • y) = star c * B x y) ∧
      (∀ x y : ℂ, B x y = star (B y x)) ∧
      (∀ x y : ℂ, B (T x) y = -B x (T y)) ∧ B (T 1) 1 ≠ 0 := by
  let B (x y : ℂ) := x * star y
  let T : ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun z => Complex.I * z
      map_add' := fun x y => mul_add _ _ _
      map_smul' := fun c z => by
        change Complex.I * (c * z) = c * (Complex.I * z)
        ring }
  refine ⟨B, T, ?_, ?_, ?_, ?_⟩
  · intro c x y
    change (c * x) * star y = c * (x * star y) ∧
      x * star (c * y) = star c * (x * star y)
    rw [star_mul]
    constructor <;> ring
  · intro x y
    change x * star y = star (y * star x)
    rw [star_mul, star_star]
  · intro x y
    change (Complex.I * x) * star y = -(x * star (Complex.I * y))
    rw [star_mul, Complex.star_def, Complex.conj_I]
    ring
  · change (Complex.I * (1 : ℂ)) * star 1 ≠ 0
    simpa using Complex.I_ne_zero

end ManuscriptAudit.TracePairing

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.TracePairing.paper10_sesquilinear_bilinear_pair_eq_zero,
      ``ManuscriptAudit.TracePairing.paper10_complex_skew_family_pair_eq_zero,
      ``ManuscriptAudit.TracePairing.paper10_complex_skew_family_eq_zero,
      ``ManuscriptAudit.TracePairing.real_part_eq_zero_of_eq_neg_star,
      ``ManuscriptAudit.TracePairing.paper10_skew_pairing_diagonal_need_not_vanish] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
