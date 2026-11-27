import Lean.Util.CollectAxioms
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.CubicKummerQuadratic

/-! Actual symmetric abscissas of the sum and difference away from the vertical chord. -/

namespace ManuscriptAudit.CubicKummerSecant

open CubicKummerQuadratic

variable {K : Type*} [Field K]

/-- The native quadratic forms give the two secant abscissas in symmetric coordinates. -/
theorem secant_forms {A x z y w : K} (hxz : x ≠ z)
    (hy : y ^ 2 = x ^ 3 + A) (hw : w ^ 2 = z ^ 3 + A) :
    let u := ((y - w) / (x - z)) ^ 2 - x - z
    let v := ((y + w) / (x - z)) ^ 2 - x - z
    forms A ![x * z, x + z, 1] = fun i => (x - z) ^ 2 * (![u * v, u + v, 1] i) := by
  let d := (x - z) ^ 2
  let u := ((y - w) / (x - z)) ^ 2 - x - z
  let v := ((y + w) / (x - z)) ^ 2 - x - z
  let b := y ^ 2 + w ^ 2 - (x + z) * d
  have hd : d ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hxz)
  have hb : b = (x + z) * x * z + 2 * A := by
    dsimp only [b, d]
    rw [hy, hw]
    ring
  have hu : d * u = b - 2 * y * w := by
    dsimp only [d, u, b]
    field_simp [sub_ne_zero.mpr hxz]
    ring
  have hv : d * v = b + 2 * y * w := by
    dsimp only [d, v, b]
    field_simp [sub_ne_zero.mpr hxz]
    ring
  have hsum : d * (u + v) = 2 * ((x + z) * (x * z)) + 4 * A := by
    rw [mul_add, hu, hv, hb]
    ring
  have hprod : d * (u * v) = (x * z) ^ 2 - 4 * A * (x + z) := by
    apply mul_left_cancel₀ hd
    calc
      d * (d * (u * v)) = (d * u) * (d * v) := by ring
      _ = b ^ 2 - 4 * y ^ 2 * w ^ 2 := by rw [hu, hv]; ring
      _ = d * ((x * z) ^ 2 - 4 * A * (x + z)) := by
        rw [hb, hy, hw]
        dsimp only [d]
        ring
  change forms A ![x * z, x + z, 1] = fun i => d * (![u * v, u + v, 1] i)
  ext i
  fin_cases i
  · simpa [forms] using hprod.symm
  · simpa [forms] using hsum.symm
  · change (x + z) ^ 2 - 4 * (x * z * 1) = d * 1
    dsimp only [d]
    ring

end ManuscriptAudit.CubicKummerSecant

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicKummerSecant.secant_forms
  let ax ← collectAxioms name
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  unless ax.all (allowed.contains ·) do
    throwError m!"{name} unexpected axioms {ax}"
  logInfo m!"{name} uses {ax}"
