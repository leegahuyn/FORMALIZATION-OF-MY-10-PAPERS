import Lean.Util.CollectAxioms
import Mathlib.Tactic.Module
import PrimalitySheafVerification.ManuscriptAudit.CubicRotationCentralizer

/-! The two rotated traces of the signed reference operator modulo four. -/

namespace ManuscriptAudit.CubicRotatedModFourTrace

open Module CubicRotationCentralizer

noncomputable section

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem rotate_coefficients (S : Module.End R V) (hSq : S ^ 2 = -S - 1) (a b : R) :
    S * (a • 1 + b • S) = (-b) • 1 + (a - b) • S := by
  calc
    _ = a • S + b • S ^ 2 := by
      simp only [mul_add, Algebra.mul_smul_comm, mul_one, pow_two]
    _ = _ := by
      rw [hSq]
      module

private theorem residue_identities :
    ∀ x : ZMod 4, x = 1 ∨ x = -1 →
      2 * (-2) - (x - 2) = x ∧
        2 * (-(x - 2)) - (-2 - (x - 2)) = -x := by decide

variable {W : Type*} [AddCommGroup W] [Module (ZMod 4) W]

/-- Given the signed reference formula (F=epsilon+2S), the two cyclic rotations
have traces (epsilon) and (-epsilon) modulo four. -/
theorem traces_of_two_rotations (B : Basis (Fin 2) (ZMod 4) W)
    (S : Module.End (ZMod 4) W) (h₀ : S (B 0) = B 1)
    (h₁ : S (B 1) = -B 0 - B 1) (hSq : S ^ 2 = -S - 1)
    (x : ZMod 4) (hx : x = 1 ∨ x = -1) :
    LinearMap.trace (ZMod 4) W (S * (x • 1 + 2 • S)) = x ∧
      LinearMap.trace (ZMod 4) W (S ^ 2 * (x • 1 + 2 • S)) = -x := by
  letI : Fact (1 < (4 : ℕ)) := ⟨by decide⟩
  constructor
  · rw [rotate_coefficients S hSq]
    exact (trace_det_of_form B S h₀ h₁ (-2) (x - 2)).1.trans (residue_identities x hx).1
  · rw [pow_two, mul_assoc, rotate_coefficients S hSq x 2,
      rotate_coefficients S hSq (-2) (x - 2)]
    exact (trace_det_of_form B S h₀ h₁ (-(x - 2)) (-2 - (x - 2))).1.trans
      (residue_identities x hx).2

end
end ManuscriptAudit.CubicRotatedModFourTrace

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicRotatedModFourTrace.traces_of_two_rotations
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
