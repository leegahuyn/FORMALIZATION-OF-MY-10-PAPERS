import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.QuadraticHeightRelation

/-! The quadratic degree of a scalar minus the cubic rotation. -/

namespace ManuscriptAudit.RotationHeightArithmetic

variable {G : Type*} [AddCommGroup G]

theorem integer_shift_height (D : QuadraticMap ℤ G ℤ) (P R : G)
    (hP : D P = 1) (hR : D R = 1) (hS : D (P+R) = 1) (c : ℤ) :
    D (c • P-R) = c^2+c+1 := by
  have hB : QuadraticMap.polar D P R = -1 := by
    simp [QuadraticMap.polar, hP, hR, hS]
  have hD : D (c • P) = c^2 := by
    simpa [hP, zsmul_eq_mul, pow_two] using D.map_smul c P
  have hS' : QuadraticMap.polar D (c • P) (-R) = c := by
    rw [QuadraticMap.polar_neg_right, QuadraticMap.polar_smul_left, hB]
    simp [zsmul_eq_mul]
  calc
    D (c • P-R) = D (c • P)+D (-R)+QuadraticMap.polar D (c • P) (-R) := by
      rw [sub_eq_add_neg]
      unfold QuadraticMap.polar
      ring
    _ = c^2+c+1 := by rw [hD, D.map_neg, hR, hS']; ring

end ManuscriptAudit.RotationHeightArithmetic

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.RotationHeightArithmetic.integer_shift_height
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun d => !allowed.contains d
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
