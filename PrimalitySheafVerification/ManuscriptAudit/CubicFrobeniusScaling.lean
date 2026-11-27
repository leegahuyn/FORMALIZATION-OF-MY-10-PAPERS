import Lean.Util.CollectAxioms
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.CubicPointScaling
import PrimalitySheafVerification.ManuscriptAudit.CubicNonsplitFrobeniusTrace

/-! Conjugation of the actual Frobenius between two centered Weierstrass twists. -/

namespace ManuscriptAudit.CubicFrobeniusScaling

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate
open CubicPointScaling CubicNonsplitFrobeniusTrace

noncomputable section

variable (E L : Type*) [Field E] [Field L] [Algebra E L] [DecidableEq L]

/-- The native endomorphism of the algebraically extended centered cubic. -/
def nativeMap (g : L →ₐ[E] L) (A : E) :
    AddMonoid.End (Curve (algebraMap E L A)).Point :=
  pointMapAt E L (Curve A) (Curve (algebraMap E L A)) (centered_baseChange E L A) g

theorem nativeMap_some (g : L →ₐ[E] L) (A : E) {x y : L}
    (h : (Curve (algebraMap E L A)).Nonsingular x y) :
    ∃ h', nativeMap E L g A (Affine.Point.some x y h) = Affine.Point.some (g x) (g y) h' := by
  exact pointMapAt_some E L (Curve A) (Curve (algebraMap E L A))
    (centered_baseChange E L A) g x y h

variable {E L}
variable {A B : E} {u v : L}

/-- The ratio g(u)/u is a sixth root of unity when u scales two base-field coefficients. -/
theorem ratio_pow (g : L →ₐ[E] L) (hu : u ≠ 0) (hA₀ : A ≠ 0)
    (hAB : u ^ 6 * algebraMap E L A = algebraMap E L B) :
    (g u / u) ^ 6 = 1 := by
  have h := congrArg g hAB
  have h' : (g u) ^ 6 * algebraMap E L A = algebraMap E L B := by
    simpa only [map_mul, map_pow, AlgHom.commutes] using h
  have hpow : (g u) ^ 6 = u ^ 6 :=
    mul_right_cancel₀ ((map_ne_zero (algebraMap E L)).mpr hA₀) (h'.trans hAB.symm)
  rw [div_pow, hpow, div_self (pow_ne_zero _ hu)]

/-- The actual map on the scaled cubic is twisted by the ratio of the two scalings. -/
theorem nativeMap_scale (g : L →ₐ[E] L) (hu : u ≠ 0) (hv : v ≠ 0)
    (hAB : u ^ 6 * algebraMap E L A = algebraMap E L B)
    (hV : v ^ 6 * algebraMap E L A = algebraMap E L A)
    (hA : (shortCubic (0 : L) (algebraMap E L A)).Δ ≠ 0)
    (hB : (shortCubic (0 : L) (algebraMap E L B)).Δ ≠ 0)
    (hg : g u = u * v) (P : (Curve (algebraMap E L A)).Point) :
    nativeMap E L g B (scaleEquiv hu hAB hA hB P) =
      scaleEquiv hu hAB hA hB (scale hv hV hA (nativeMap E L g A P)) := by
  cases P with
  | zero =>
    change nativeMap E L g B (scaleEquiv hu hAB hA hB 0) =
      scaleEquiv hu hAB hA hB (scale hv hV hA (nativeMap E L g A 0))
    simp only [map_zero]
  | some x y hP =>
    rw [scaleEquiv_some hu hAB hA hB hP]
    obtain ⟨hA', eA⟩ := nativeMap_some E L g A hP
    obtain ⟨hB', eB⟩ := nativeMap_some E L g B (scaled_nonsingular hAB hB hP)
    rw [eA, eB, scale_some, scaleEquiv_some, Affine.Point.some.injEq]
    constructor
    · rw [map_mul, map_pow, hg]
      ring
    · rw [map_mul, map_pow, hg]
      ring

end
end ManuscriptAudit.CubicFrobeniusScaling

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicFrobeniusScaling.ratio_pow,
      ``ManuscriptAudit.CubicFrobeniusScaling.nativeMap_scale] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
