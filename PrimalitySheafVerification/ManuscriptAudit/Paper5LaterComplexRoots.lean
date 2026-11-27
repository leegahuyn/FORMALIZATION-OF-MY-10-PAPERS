import Lean.Util.CollectAxioms
import Mathlib.Data.Complex.Basic
import PrimalitySheafVerification.ManuscriptAudit.Paper5LaterRoundedEigenvalues

/-! Exact conjugate roots of the integer quadratics underlying the later numerical table. -/

namespace ManuscriptAudit.Paper5LaterComplexRoots

open Paper5LaterTables Paper5LaterRoundedEigenvalues

noncomputable section

/-- The upper and lower roots have the exact displayed real coordinate and opposite ordinates. -/
def displayedRoot (r : TateRow) (upper : Bool) : ℂ :=
  ⟨(r.trace : ℝ) / 2, if upper then Real.sqrt (radicand r) / 2
    else -(Real.sqrt (radicand r) / 2)⟩

theorem exact_quadratic_roots {r : TateRow} (h : 0 ≤ radicand r) (upper : Bool) :
    displayedRoot r upper ^ 2 - (r.trace : ℂ) * displayedRoot r upper +
      (r.determinant : ℂ) = 0 := by
  have hD : (radicand r : ℝ) = 4 * (r.determinant : ℝ) - (r.trace : ℝ)^2 := by
    push_cast [radicand] <;> rfl
  have h0 : (0 : ℝ) ≤ (radicand r : ℝ) := by exact_mod_cast h
  have hSq : (displayedRoot r upper).im ^ 2 = (radicand r : ℝ) / 4 := by
    have hs := Real.sq_sqrt h0
    cases upper <;> simp [displayedRoot, div_pow, hs] <;> ring
  have hRe : (displayedRoot r upper).re = (r.trace : ℝ) / 2 := rfl
  apply Complex.ext
  · simp only [pow_two, Complex.add_re, Complex.sub_re, Complex.mul_re,
      Complex.intCast_re, Complex.intCast_im, Complex.natCast_re, Complex.zero_re, zero_mul,
      sub_zero, hRe]
    nlinarith only [hSq, hD]
  · simp only [pow_two, Complex.add_im, Complex.sub_im, Complex.mul_im,
      Complex.intCast_re, Complex.intCast_im, Complex.natCast_im, Complex.zero_im,
      zero_mul, add_zero, hRe]
    ring

theorem conjugate_roots (r : TateRow) :
    star (displayedRoot r true) = displayedRoot r false := by
  apply Complex.ext <;> simp [displayedRoot]

theorem two_distinct_roots {r : TateRow} (h : 0 < radicand r) :
    displayedRoot r true ≠ displayedRoot r false := by
  intro he
  have h₀ : (0 : ℝ) < (radicand r : ℝ) := by exact_mod_cast h
  have hp := Real.sqrt_pos.2 h₀
  have hi := congrArg Complex.im he
  change Real.sqrt (radicand r) / 2 = -(Real.sqrt (radicand r) / 2) at hi
  linarith

end
end ManuscriptAudit.Paper5LaterComplexRoots

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5LaterComplexRoots.exact_quadratic_roots,
      ``ManuscriptAudit.Paper5LaterComplexRoots.conjugate_roots,
      ``ManuscriptAudit.Paper5LaterComplexRoots.two_distinct_roots] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
