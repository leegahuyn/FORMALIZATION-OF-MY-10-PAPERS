import Lean.Util.CollectAxioms
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Module.LinearMap.Basic

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

end ManuscriptAudit.TracePairing

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.TracePairing.paper10_sesquilinear_bilinear_pair_eq_zero,
      ``ManuscriptAudit.TracePairing.paper10_complex_skew_family_pair_eq_zero,
      ``ManuscriptAudit.TracePairing.paper10_complex_skew_family_eq_zero] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
