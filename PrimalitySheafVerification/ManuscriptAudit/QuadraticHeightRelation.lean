import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! A quadratic height yields the characteristic relation from two required degree identities. -/

namespace ManuscriptAudit.QuadraticHeightRelation

variable {G : Type*} [AddCommGroup G]

/-- The height of the candidate characteristic relation vanishes at a point of height one.
Only the scaling identity for F and the single squared-degree identity for F+1 are needed. -/
theorem height_characteristic_relation (D : QuadraticMap ℤ G ℤ) (F : G →+ G)
    (P : G) (q : ℤ) (hP : D P = 1)
    (hScale : ∀ X : G, D (F X) = q * D X)
    (hSquare : D (F (F P + P) + (F P + P)) = D (F P + P) ^ 2) :
    let t := q + 1 - D (F P - P)
    D (F (F P) - t • F P + q • P) = 0 := by
  let B := QuadraticMap.polar D
  let t := B (F P) P
  have hAdd (x y : G) : D (x + y) = D x + D y + B x y := by
    dsimp only [B, QuadraticMap.polar]
    ring
  have hAdd₃ (x y z : G) :
      D (x + y + z) = D x + D y + D z + B x y + B x z + B y z := by
    rw [hAdd (x + y) z, hAdd x y]
    have hb : B (x + y) z = B x z + B y z := QuadraticMap.polar_add_left D x y z
    rw [hb]
    ring
  have hSMul (a : ℤ) (x : G) : D (a • x) = a ^ 2 * D x := by
    simpa [zsmul_eq_mul, pow_two] using D.map_smul a x
  have hBL (a : ℤ) (x y : G) : B (a • x) y = a * B x y := by
    simpa [zsmul_eq_mul, B] using QuadraticMap.polar_smul_left D a x y
  have hBR (a : ℤ) (x y : G) : B x (a • y) = a * B x y := by
    simpa [zsmul_eq_mul, B] using QuadraticMap.polar_smul_right D a x y
  have hFPolar (x y : G) : B (F x) (F y) = q * B x y := by
    change D (F x + F y) - D (F x) - D (F y) = q * (D (x + y) - D x - D y)
    rw [← map_add, hScale, hScale, hScale]
    ring
  have hDP : D (F P) = q := by rw [hScale, hP, mul_one]
  have hD₂P : D (F (F P)) = q ^ 2 := by rw [hScale, hDP, pow_two]
  have hB₂P : B (F (F P)) (F P) = q * t := hFPolar (F P) P
  have hDPlus : D (F P + P) = q + 1 + t := by rw [hAdd, hDP, hP]
  have hGroup : F (F P + P) + (F P + P) = F (F P) + (2 : ℤ) • F P + P := by
    rw [map_add, two_smul ℤ]
    abel
  have hSq : (q + 1 + t) ^ 2 =
      q ^ 2 + 4 * q + 1 + 2 * q * t + B (F (F P)) P + 2 * t := by
    calc
      _ = D (F (F P + P) + (F P + P)) := by rw [hSquare, hDPlus]
      _ = D (F (F P) + (2 : ℤ) • F P + P) := congrArg D hGroup
      _ = _ := by simp only [hAdd₃, hD₂P, hDP, hP, hSMul, hBL, hBR, hB₂P]; ring
  have hBTrace : B (F (F P)) P = t ^ 2 - 2 * q := by nlinarith only [hSq]
  have hTrace : q + 1 - D (F P - P) = t := by
    have hNeg : B (F P) (-P) = -t := QuadraticMap.polar_neg_right D (F P) P
    rw [sub_eq_add_neg, hAdd, D.map_neg, hDP, hP, hNeg]
    ring
  dsimp only
  rw [hTrace, sub_eq_add_neg, ← neg_zsmul, hAdd₃]
  simp only [hD₂P, hDP, hP, hSMul, hBL, hBR, hB₂P, hBTrace]
  ring

end ManuscriptAudit.QuadraticHeightRelation

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.QuadraticHeightRelation.height_characteristic_relation
  let ax ← collectAxioms name
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  unless ax.all (allowed.contains ·) do
    throwError m!"{name} unexpected axioms {ax}"
  logInfo m!"{name} uses {ax}"
