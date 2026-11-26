import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.FieldTheory.IsAlgClosed.Basic
import PrimalitySheafVerification.ManuscriptAudit.AffineLineDivisor

/-!
# The exact global-section divisor sequence of the affine line

Over an algebraically closed ground field all finite closed points
are represented by linear polynomials. A nonzero rational function
with no finite divisor is a constant unit.
-/

namespace ManuscriptAudit.AffineLineDivisor

noncomputable section

variable (K : Type*) [Field K]

/-- The inclusion of constant units in the rational function field. -/
def constantUnits : Additive Kˣ →+ Additive (RatFunc K)ˣ :=
  (Units.map (algebraMap K (RatFunc K)).toMonoidHom).toAdditive

theorem constantUnits_injective : Function.Injective (constantUnits K) := by
  intro x y h
  apply Additive.ext
  apply Units.ext
  apply (algebraMap K (RatFunc K)).injective
  exact congrArg (fun a : Additive (RatFunc K)ˣ => (a.toMul : RatFunc K)) h

private theorem constant_eq_polyMap (a : K) :
    algebraMap K (RatFunc K) a =
      algebraMap (Polynomial K) (RatFunc K) (Polynomial.C a) :=
  IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K) a

/-- The kernel of the actual finite divisor map consists of constant units. -/
theorem divisor_exact [IsAlgClosed K] : Function.Exact (constantUnits K) (divisor K) := by
  intro x
  constructor
  · intro hx
    let z : RatFunc K := x.toMul
    have hn : z.num ≠ 0 := RatFunc.num_ne_zero x.toMul.ne_zero
    have hroots : z.num.roots = z.denom.roots :=
      roots_eq_of_rootCycle_eq K (sub_eq_zero.mp hx)
    let c := z.num.leadingCoeff
    have hnum : z.num = Polynomial.C c * z.denom := by
      have hn' := (IsAlgClosed.splits z.num).eq_prod_roots
      have hd' := (IsAlgClosed.splits z.denom).eq_prod_roots_of_monic z.monic_denom
      exact hn'.trans (by rw [hroots, ← hd'])
    have hc : c ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hn
    refine ⟨Additive.ofMul (Units.mk0 c hc), ?_⟩
    apply Additive.ext
    apply Units.ext
    change algebraMap K (RatFunc K) c = z
    calc
      _ = algebraMap (Polynomial K) (RatFunc K) (Polynomial.C c) := constant_eq_polyMap K c
      _ = (algebraMap (Polynomial K) (RatFunc K) (Polynomial.C c) *
          algebraMap (Polynomial K) (RatFunc K) z.denom) /
          algebraMap (Polynomial K) (RatFunc K) z.denom :=
        (mul_div_cancel_right₀ _ (RatFunc.algebraMap_ne_zero z.denom_ne_zero)).symm
      _ = z := by rw [← map_mul, ← hnum, RatFunc.num_div_denom]
  · rintro ⟨a, rfl⟩
    let c : K := a.toMul
    change rootCycle K (RatFunc.num (algebraMap K (RatFunc K) c)) -
      rootCycle K (RatFunc.denom (algebraMap K (RatFunc K) c)) = 0
    rw [constant_eq_polyMap, RatFunc.num_algebraMap, RatFunc.denom_algebraMap,
      rootCycle_C, rootCycle_one, sub_zero]

end

end ManuscriptAudit.AffineLineDivisor

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineLineDivisor.constantUnits_injective,
      ``ManuscriptAudit.AffineLineDivisor.divisor_exact] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
