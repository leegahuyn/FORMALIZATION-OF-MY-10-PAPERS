import Lean.Util.CollectAxioms
import Mathlib.Tactic.LinearCombination
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinarySeven

/-! Exact characteristic-seven tangent and secant identities on y² = x³ + 5. -/

namespace ManuscriptAudit.Paper5OrdinarySevenSecant

open Paper5OrdinarySeven

noncomputable section

variable {F : Type*} [Field F] [CharP F 7]

theorem two_ne : (2 : F) ≠ 0 := by
  change ((2 : ℕ) : F) ≠ 0
  rw [ne_eq, CharP.cast_eq_zero_iff F 7 2]
  decide

def tangent (x y : F) : F := 3 * x ^ 2 / (2 * y)

def doubleX (x y : F) : F := tangent x y ^ 2 - x - x

def doubleY (x y : F) : F := -(tangent x y * (doubleX x y - x) + y)

def chord (x y : F) : F := -tangent x y * (1 + y ^ 2)

private theorem tangent_mul {x y : F} (hy : y ≠ 0) :
    (2 * y) * tangent x y = 3 * x ^ 2 := by
  unfold tangent
  exact mul_div_cancel₀ _ (mul_ne_zero two_ne hy)

private theorem tangent_sq_mul {x y : F} (hy : y ≠ 0) :
    tangent x y ^ 2 * y ^ 2 = 4 * x ^ 4 := by
  have h := congrArg (fun t : F => t ^ 2) (tangent_mul (x := x) hy)
  linear_combination (2 : F) * h - (tangent x y ^ 2 * y ^ 2 - 2 * x ^ 4) * seven_zero F

theorem doubleX_gap {x y : F} (hy : y ≠ 0) (he : y ^ 2 = x ^ 3 + 5) :
    (doubleX x y - 2 * x) * y ^ 2 = x := by
  unfold doubleX
  linear_combination tangent_sq_mul (x := x) hy - (4 * x) * he - (3 * x) * seven_zero F

theorem abscissas_ne {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) (he : y ^ 2 = x ^ 3 + 5) :
    2 * x ≠ doubleX x y := by
  intro h
  have hg := doubleX_gap hy he
  rw [← h, sub_self, zero_mul] at hg
  exact hx hg.symm

theorem actual_chord {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) (he : y ^ 2 = x ^ 3 + 5) :
    (-y - doubleY x y) / (2 * x - doubleX x y) = chord x y := by
  apply (div_eq_iff (sub_ne_zero.mpr (abscissas_ne hx hy he))).mpr
  unfold doubleY chord
  linear_combination -(tangent x y) * doubleX_gap hy he

theorem chord_abscissa {x y : F} (hy : y ≠ 0) (he : y ^ 2 = x ^ 3 + 5) :
    chord x y ^ 2 - 2 * x - doubleX x y = 4 * x ^ 7 := by
  calc
    _ = (tangent x y ^ 2 * y ^ 2) * (2 + y ^ 2) := by unfold chord doubleX; ring
    _ = _ := by
      rw [tangent_sq_mul hy, he]
      linear_combination (4 * x ^ 4) * seven_zero F

theorem chord_ordinate {x y : F} (hy : y ≠ 0) (he : y ^ 2 = x ^ 3 + 5) :
    -(chord x y * (4 * x ^ 7 - 2 * x) + -y) = -y ^ 7 := by
  let t := y ^ 2
  have hXT : x ^ 3 = t - 5 := by dsimp only [t]; linear_combination -he
  have hFactor : 4 * x ^ 7 - 2 * x = x * (2 * t * (2 * t + 1)) := by
    calc
      _ = x * (4 * (x ^ 3) ^ 2 - 2) := by ring
      _ = _ := by
        rw [hXT]
        linear_combination (x * (14 - 6 * t)) * seven_zero F
  calc
    _ = tangent x y * (1 + t) * (x * (2 * t * (2 * t + 1))) + y := by
      rw [chord, hFactor]
      change _ = tangent x y * (1 + t) * (x * (2 * t * (2 * t + 1))) + y
      dsimp only [t]
      ring
    _ = ((2 * y) * tangent x y) * (x * y * (1 + t) * (2 * t + 1)) + y := by
      dsimp only [t]
      ring
    _ = y * (3 * x ^ 3 * (1 + t) * (2 * t + 1) + 1) := by
      rw [tangent_mul hy]
      ring
    _ = y * (-(t ^ 3)) := by
      rw [hXT]
      linear_combination (y * (t ^ 3 - 3 * t ^ 2 - 6 * t - 2)) * seven_zero F
    _ = _ := by dsimp only [t]; ring

end
end ManuscriptAudit.Paper5OrdinarySevenSecant

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5OrdinarySevenSecant.doubleX_gap,
      ``ManuscriptAudit.Paper5OrdinarySevenSecant.abscissas_ne,
      ``ManuscriptAudit.Paper5OrdinarySevenSecant.actual_chord,
      ``ManuscriptAudit.Paper5OrdinarySevenSecant.chord_abscissa,
      ``ManuscriptAudit.Paper5OrdinarySevenSecant.chord_ordinate] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
