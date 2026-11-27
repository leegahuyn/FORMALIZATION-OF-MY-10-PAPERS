import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! An integer-valued parallelogram height has a native quadratic-map structure. -/

namespace ManuscriptAudit.IntegerHeightQuadraticMap

variable {G : Type*} [AddCommGroup G]

/-- The parallelogram equation and value at zero make an integer-valued height quadratic. -/
def ofParallelogram (d : G → ℤ) (h₀ : d 0 = 0)
    (hP : ∀ x y : G, d (x + y) + d (x - y) = 2 * d x + 2 * d y) :
    QuadraticMap ℤ G ℤ := by
  let J (x y : G) := d (x + y) - d (x - y)
  have hNeg (x : G) : d (-x) = d x := by
    have h := hP 0 x
    rw [zero_add, zero_sub, h₀] at h
    omega
  have hJNeg (x y : G) : J (-x) y = -J x y := by
    change d (-x + y) - d (-x - y) = -(d (x + y) - d (x - y))
    rw [show -x + y = -(x - y) by abel, show -x - y = -(x + y) by abel, hNeg, hNeg]
    omega
  have hJensen (x z y : G) : J (x + z) y + J (x - z) y = 2 * J x y := by
    change (d (x + z + y) - d (x + z - y)) +
        (d (x - z + y) - d (x - z - y)) = 2 * (d (x + y) - d (x - y))
    rw [show x + z + y = x + y + z by abel, show x + z - y = x - y + z by abel,
      show x - z + y = x + y - z by abel, show x - z - y = x - y - z by abel]
    have hL := hP (x + y) z
    have hR := hP (x - y) z
    omega
  have hJAdd (x z y : G) : J (x + z) y = J x y + J z y := by
    have hL := hJensen x z y
    have hR := hJensen z x y
    rw [add_comm z x, show z - x = -(x - z) by abel, hJNeg] at hR
    omega
  let B := QuadraticMap.polar d
  have hJB (x y : G) : J x y = 2 * B x y := by
    change d (x + y) - d (x - y) = 2 * (d (x + y) - d x - d y)
    have h := hP x y
    omega
  have hBAdd (x z y : G) : B (x + z) y = B x y + B z y := by
    have h := hJAdd x z y
    rw [hJB, hJB, hJB] at h
    omega
  have hBZero (y : G) : B 0 y = 0 := by simp [B, QuadraticMap.polar, h₀]
  let bHom (y : G) : G →+ ℤ :=
    { toFun := fun x => B x y
      map_zero' := hBZero y
      map_add' := fun x z => hBAdd x z y }
  have hBL (a : ℤ) (x y : G) : B (a • x) y = a • B x y :=
    (bHom y).map_zsmul a x
  have hBC (x y : G) : B x y = B y x := QuadraticMap.polar_comm d x y
  have hBR (a : ℤ) (x y : G) : B x (a • y) = a • B x y := by
    rw [hBC x, hBL, hBC y]
  have hDiag (x : G) : B x x = 2 * d x := by
    change d (x + x) - d x - d x = 2 * d x
    have h := hP x x
    rw [sub_self, h₀] at h
    omega
  apply QuadraticMap.ofPolar d _ hBAdd hBL
  intro a x
  have hTwo : 2 * d (a • x) = (a * a) * (2 * d x) := by
    rw [← hDiag (a • x), hBL, hBR, hDiag]
    simp only [zsmul_eq_mul, Int.cast_id]
    ring
  change d (a • x) = (a * a) • d x
  simp only [zsmul_eq_mul, Int.cast_id]
  nlinarith only [hTwo]

@[simp]
theorem ofParallelogram_apply (d : G → ℤ) (h₀ : d 0 = 0)
    (hP : ∀ x y : G, d (x + y) + d (x - y) = 2 * d x + 2 * d y) (x : G) :
    ofParallelogram d h₀ hP x = d x := rfl

end ManuscriptAudit.IntegerHeightQuadraticMap

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.IntegerHeightQuadraticMap.ofParallelogram_apply
  let ax ← collectAxioms name
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  unless ax.all (allowed.contains ·) do
    throwError m!"{name} unexpected axioms {ax}"
  logInfo m!"{name} uses {ax}"
