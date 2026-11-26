import Lean.Util.CollectAxioms
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import PrimalitySheafVerification.ManuscriptAudit.InverseHalfNormDescent
import PrimalitySheafVerification.ManuscriptAudit.LiteralCuspTruncation

/-!
# The invariant pointwise norm for inverse half-weight automorphy

The actual transformation law for the printed −1/2 factor multiplies
the squared pointwise norm by the inverse of |cz+d|. The square root
of height transforms by the same factor. Dividing by that square root
gives a function on the actual Γ(2) orbit quotient.
-/

namespace ManuscriptAudit.InverseHalfInvariantNorm

open UpperHalfPlane InverseHalfNormDescent LiteralCuspTruncation
open scoped MatrixGroups

noncomputable section

/-- The metric density for the inverse-half transformation law. -/
def pointwiseMetric (u : ℍ → ℂ) (z : ℍ) : ℝ :=
  ‖u z‖ ^ (2 : ℕ) / Real.sqrt z.im

private theorem denominator_norm_ne_zero (g : SL(2, ℤ)) (z : ℍ) :
    ‖denom g z‖ ≠ 0 := by
  intro h
  have hPos := (g • z).im_pos
  rw [ModularGroup.im_smul_eq_div_normSq, ← Complex.sq_norm, h] at hPos
  simpa using hPos

/-- The actual squared norm with its square-root height denominator is invariant. -/
theorem pointwiseMetric_invariant
    (u : ℍ → ℂ) (ν : SL(2, ℤ) → ℂ)
    (hPhase : ∀ g ∈ GammaTwo, ‖ν g‖ = 1)
    (hAut : ∀ g ∈ GammaTwo, ∀ z : ℍ,
      u (g • z) = ν g * (denom g z) ^ ((-(1 / 2 : ℝ)) : ℂ) * u z)
    (g : SL(2, ℤ)) (hg : g ∈ GammaTwo) (z : ℍ) :
    pointwiseMetric u (g • z) = pointwiseMetric u z := by
  have hScaled : ‖u (g • z)‖ ^ (2 : ℕ) =
      ‖denom g z‖⁻¹ * ‖u z‖ ^ (2 : ℕ) := by
    rw [hAut g hg z, norm_mul, norm_mul, hPhase g hg, one_mul, mul_pow,
      inverseHalf_norm_sq]
  have hd := denominator_norm_ne_zero g z
  have hs : Real.sqrt z.im ≠ 0 := (Real.sqrt_pos.2 z.im_pos).ne'
  unfold pointwiseMetric
  rw [hScaled, ModularGroup.im_smul_eq_div_normSq, ← Complex.sq_norm,
    Real.sqrt_div z.im_pos.le, Real.sqrt_sq (norm_nonneg _)]
  field_simp [hd, hs] <;> ring

/-- The corrected norm density on the actual Γ(2) orbit quotient. -/
def quotientPointwiseMetric
    (u : ℍ → ℂ) (ν : SL(2, ℤ) → ℂ)
    (hPhase : ∀ g ∈ GammaTwo, ‖ν g‖ = 1)
    (hAut : ∀ g ∈ GammaTwo, ∀ z : ℍ,
      u (g • z) = ν g * (denom g z) ^ ((-(1 / 2 : ℝ)) : ℂ) * u z) :
    OrbitQuotient → ℝ :=
  Quotient.lift (pointwiseMetric u) (by
    rintro z w ⟨g, rfl⟩
    exact pointwiseMetric_invariant u ν hPhase hAut g.val g.property w)

theorem quotientPointwiseMetric_apply
    (u : ℍ → ℂ) (ν : SL(2, ℤ) → ℂ)
    (hPhase : ∀ g ∈ GammaTwo, ‖ν g‖ = 1)
    (hAut : ∀ g ∈ GammaTwo, ∀ z : ℍ,
      u (g • z) = ν g * (denom g z) ^ ((-(1 / 2 : ℝ)) : ℂ) * u z)
    (z : ℍ) :
    quotientPointwiseMetric u ν hPhase hAut (orbitPoint z) = pointwiseMetric u z :=
  rfl

/-- The pointwise sesquilinear pairing with the corrected height factor. -/
def pointwisePairing (u v : ℍ → ℂ) (z : ℍ) : ℂ :=
  u z * star (v z) / (Real.sqrt z.im : ℂ)

theorem pointwisePairing_invariant
    (u v : ℍ → ℂ) (ν : SL(2, ℤ) → ℂ)
    (hPhase : ∀ g ∈ GammaTwo, ‖ν g‖ = 1)
    (hU : ∀ g ∈ GammaTwo, ∀ z : ℍ,
      u (g • z) = ν g * (denom g z) ^ ((-(1 / 2 : ℝ)) : ℂ) * u z)
    (hV : ∀ g ∈ GammaTwo, ∀ z : ℍ,
      v (g • z) = ν g * (denom g z) ^ ((-(1 / 2 : ℝ)) : ℂ) * v z)
    (g : SL(2, ℤ)) (hg : g ∈ GammaTwo) (z : ℍ) :
    pointwisePairing u v (g • z) = pointwisePairing u v z := by
  let c := ν g * (denom g z) ^ ((-(1 / 2 : ℝ)) : ℂ)
  have hNorm : ‖c‖ ^ (2 : ℕ) = ‖denom g z‖⁻¹ := by
    dsimp [c]
    rw [norm_mul, hPhase g hg, one_mul, inverseHalf_norm_sq]
  have hConj : c * star c = ((‖denom g z‖⁻¹ : ℝ) : ℂ) := by
    calc
      c * star c = (Complex.normSq c : ℂ) := by
        simpa only [Complex.star_def] using Complex.mul_conj c
      _ = _ := by rw [← Complex.sq_norm, hNorm]
  have hNumerator : u (g • z) * star (v (g • z)) =
      (c * star c) * (u z * star (v z)) := by
    rw [show u (g • z) = c * u z from hU g hg z, show v (g • z) = c * v z from hV g hg z,
      star_mul]
    ring
  have hd : (‖denom g z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (denominator_norm_ne_zero g z)
  have hs : (Real.sqrt z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 z.im_pos).ne'
  unfold pointwisePairing
  rw [hNumerator, hConj, ModularGroup.im_smul_eq_div_normSq, ← Complex.sq_norm,
    Real.sqrt_div z.im_pos.le, Real.sqrt_sq (norm_nonneg _), Complex.ofReal_div, Complex.ofReal_inv]
  field_simp [hd, hs] <;> ring

theorem pointwisePairing_self (u : ℍ → ℂ) (z : ℍ) :
    pointwisePairing u u z = (pointwiseMetric u z : ℂ) := by
  unfold pointwisePairing pointwiseMetric
  rw [Complex.star_def, Complex.mul_conj, ← Complex.sq_norm, Complex.ofReal_div]

/-- The corrected integrand for two inverse-half sections on the actual quotient. -/
def quotientPointwisePairing
    (u v : ℍ → ℂ) (ν : SL(2, ℤ) → ℂ)
    (hPhase : ∀ g ∈ GammaTwo, ‖ν g‖ = 1)
    (hU : ∀ g ∈ GammaTwo, ∀ z : ℍ,
      u (g • z) = ν g * (denom g z) ^ ((-(1 / 2 : ℝ)) : ℂ) * u z)
    (hV : ∀ g ∈ GammaTwo, ∀ z : ℍ,
      v (g • z) = ν g * (denom g z) ^ ((-(1 / 2 : ℝ)) : ℂ) * v z) :
    OrbitQuotient → ℂ :=
  Quotient.lift (pointwisePairing u v) (by
    rintro z w ⟨g, rfl⟩
    exact pointwisePairing_invariant u v ν hPhase hU hV g.val g.property w)

end

end ManuscriptAudit.InverseHalfInvariantNorm

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.InverseHalfInvariantNorm.pointwiseMetric_invariant,
      ``ManuscriptAudit.InverseHalfInvariantNorm.quotientPointwiseMetric_apply,
      ``ManuscriptAudit.InverseHalfInvariantNorm.pointwisePairing_invariant,
      ``ManuscriptAudit.InverseHalfInvariantNorm.pointwisePairing_self,
      ``ManuscriptAudit.InverseHalfInvariantNorm.quotientPointwisePairing] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
