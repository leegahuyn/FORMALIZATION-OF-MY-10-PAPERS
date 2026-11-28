import Lean.Util.CollectAxioms
import Mathlib.Analysis.InnerProductSpace.Basic

/-! The scalar product of a positive real form on its genuine graph norm. -/

namespace ManuscriptAudit.RealFormInnerProduct

noncomputable section

variable {D : Type*} [AddCommGroup D] [Module ℝ D]

/-- The form defines the inner product on the normed group built from its diagonal. -/
def innerProductSpace (P : InnerProductSpace.Core ℝ D) :
    letI := P.toNormedAddCommGroup
    InnerProductSpace ℝ D := by
  letI := P.toNormedAddCommGroup
  have hSym (x y : D) : P.inner y x = P.inner x y := P.conj_inner_symm x y
  have hLeft (x y : D) (r : ℝ) : P.inner (r • x) y = r * P.inner x y := P.smul_left x y r
  have hRight (x y : D) (r : ℝ) : P.inner x (r • y) = r * P.inner x y := by
    rw [← hSym x (r • y), hLeft, hSym x y]
  let S : NormedSpace ℝ D :=
    { norm_smul_le := fun r x => by
        change Real.sqrt (P.inner (r • x) (r • x)) ≤ ‖r‖ * Real.sqrt (P.inner x x)
        rw [hLeft, hRight, ← mul_assoc, ← sq, Real.sqrt_mul (sq_nonneg r),
          Real.sqrt_sq_eq_abs, Real.norm_eq_abs] }
  exact
    { toNormedSpace := S
      inner := P.inner
      norm_sq_eq_re_inner := fun x => Real.sq_sqrt (P.re_inner_nonneg x)
      conj_inner_symm := P.conj_inner_symm
      add_left := P.add_left
      smul_left := P.smul_left }

/-- The squared norm is exactly the shifted form diagonal in this model. -/
theorem norm_sq_eq (P : InnerProductSpace.Core ℝ D) (x : D) :
    letI := P.toNormedAddCommGroup
    ‖x‖ ^ 2 = P.inner x x := by
  letI := P.toNormedAddCommGroup
  exact Real.sq_sqrt (P.re_inner_nonneg x)

end
end ManuscriptAudit.RealFormInnerProduct

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.RealFormInnerProduct.innerProductSpace,
      ``ManuscriptAudit.RealFormInnerProduct.norm_sq_eq] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
