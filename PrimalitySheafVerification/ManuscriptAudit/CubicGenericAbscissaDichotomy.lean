import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicGenericZeroHeight

/-! A generic anti-invariant point is two-torsion or has transcendental abscissa. -/

namespace ManuscriptAudit.CubicGenericAbscissaDichotomy

open WeierstrassCurve CubicGenericFunctionField CubicGenericAntiInvariant
open CubicGenericZeroHeight CubicGenericPointHeight RationalSubstitutionDegree

noncomputable section
open scoped Classical

variable {K : Type*} [Field K] {A : K}

/-- Every positive-height anti-invariant affine point has a nonconstant rational abscissa. -/
theorem transcendental_of_height_ne_zero (h₂ : (2 : K) ≠ 0)
    {x y : Model A} {hP : (CubicThreeTorsionOrdinate.Curve
      (algebraMap K (Model A) A)).Nonsingular x y}
    (h : (Affine.Point.some x y hP : Points A) ∈ antiInvariant A)
    (hHeight : height A ⟨.some x y hP, h⟩ ≠ 0) : Transcendental K x := by
  have h₂R : (2 : RatFunc K) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K (RatFunc K))).mpr h₂
  obtain ⟨r, hr⟩ := exists_algebraMap_of_fixed h₂R (abscissa_fixed A h)
  have hre : r = x.re := congrArg QuadraticAlgebra.re hr
  have hn : ¬ ∃ c : K, r = RatFunc.C c := by
    rintro ⟨c, hc⟩
    apply hHeight
    change rationalDegree x.re = 0
    rw [← hre]
    exact Nat.max_eq_zero_iff.mpr ((RatFunc.eq_C_iff r).mp ⟨c, hc⟩)
  rw [← hr]
  exact (transcendental_algebraMap_iff (algebraMap (RatFunc K) (Model A)).injective).mpr
    (r.transcendental_of_ne_C hn)

/-- The only generic anti-invariant points with algebraic abscissa are killed by doubling. -/
theorem two_torsion_or_transcendental (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (hA : A ≠ 0) (P : antiInvariant A) : (2 : ℕ) • P = 0 ∨
      ∃ (x y : Model A) (hP : (CubicThreeTorsionOrdinate.Curve
        (algebraMap K (Model A) A)).Nonsingular x y),
      P.val = .some x y hP ∧ Transcendental K x := by
  by_cases hHeight : height A P = 0
  · exact Or.inl (two_nsmul_eq_zero_of_height_zero A h₂ h₃ hA P hHeight)
  · right
    obtain ⟨P, hP⟩ := P
    cases P with
    | zero =>
      apply (hHeight (height_zero A)).elim
    | some x y hxy =>
      exact ⟨x, y, hxy, rfl, transcendental_of_height_ne_zero h₂ hP hHeight⟩

end

end ManuscriptAudit.CubicGenericAbscissaDichotomy

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.CubicGenericAbscissaDichotomy.transcendental_of_height_ne_zero,
      ``ManuscriptAudit.CubicGenericAbscissaDichotomy.two_torsion_or_transcendental] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
