import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicGenericPointHeight
import PrimalitySheafVerification.ManuscriptAudit.RationalSubstitutionDegree

/-! Generic rational coordinate heights over arbitrary fields. -/

namespace ManuscriptAudit.CubicRationalPointHeight

open Polynomial WeierstrassCurve CubicGenericFunctionField CubicGenericAntiInvariant
open CubicGenericPointHeight RationalSubstitutionDegree

noncomputable section
open scoped Classical

variable {K : Type*} [Field K] (A : K)

/-- A finite projective representative with rational abscissa has its normalized rational degree. -/
theorem height_eq_of_xRep (P : antiInvariant A) (r : RatFunc K)
    (hRep : P.val.xRep = ![algebraMap (RatFunc K) (Model A) r, 1]) :
    height A P = rationalDegree r := by
  obtain ⟨P, hP⟩ := P
  cases P with
  | zero =>
    have he := congrFun hRep 1
    change (0 : Model A) = 1 at he
    exact (zero_ne_one he).elim
  | some x y hp =>
    have he := congrFun hRep 0
    change x = algebraMap (RatFunc K) (Model A) r at he
    have hx : x.re = r := congrArg QuadraticAlgebra.re he
    change rationalDegree x.re = rationalDegree r
    rw [hx]

/-- The generic affine point itself has height one over an arbitrary field. -/
theorem generic_point_height (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0) :
    height A ⟨genericPoint A h₂ h₃ hA, genericPoint_mem_antiInvariant A h₂ h₃ hA⟩ = 1 := by
  change rationalDegree (RatFunc.X : RatFunc K) = 1
  simp only [rationalDegree, RatFunc.num_X, RatFunc.denom_X, natDegree_X, natDegree_one, max_zero_right]

end

end ManuscriptAudit.CubicRationalPointHeight

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.CubicRationalPointHeight.height_eq_of_xRep,
      ``ManuscriptAudit.CubicRationalPointHeight.generic_point_height] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
