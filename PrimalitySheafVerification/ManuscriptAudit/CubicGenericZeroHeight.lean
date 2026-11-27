import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.CubicGenericPointHeight
import PrimalitySheafVerification.ManuscriptAudit.RationalSubstitutionDegree

/-! Zero abscissa height on the actual anti-invariant group implies two-torsion. -/

namespace ManuscriptAudit.CubicGenericZeroHeight

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate CubicTwoTorsion
open CubicNonsplitFrobeniusTrace CubicGenericFunctionField CubicGenericAntiInvariant
open CubicGenericPointHeight RationalSubstitutionDegree

noncomputable section
open scoped Classical

variable {K : Type*} [Field K] (A : K)

private theorem ordinate_antifixed {x y : Model A}
    {hP : (Curve (algebraMap K (Model A) A)).Nonsingular x y}
    (h : (Affine.Point.some x y hP : Points A) ∈ antiInvariant A) :
    conjugation A y = -y := by
  change sigma A (.some x y hP) = -(.some x y hP : Points A) at h
  obtain ⟨h', he⟩ := pointMapAt_some K (Model A) (Curve A) (Curve (algebraMap K (Model A) A))
    (centered_baseChange K (Model A) A) ((conjugation A).restrictScalars K) x y hP
  change sigma A (.some x y hP) = .some (conjugation A x) (conjugation A y) h' at he
  rw [he, Affine.Point.neg_some, some_eq_iff A] at h
  simpa [Curve, CubicAffine, shortCubic, Affine.negY] using h.2

private theorem pure_square_constant {y : Model A} {d : K} (hr : y.re = 0)
    (hY : y ^ 2 = algebraMap K (Model A) d) : y = 0 := by
  have hProd : (y ^ 2).re = (y.im ^ 2) * radicand A := by
    rw [pow_two, QuadraticAlgebra.re_mul, hr]
    ring
  have h := congrArg QuadraticAlgebra.re hY
  change (y ^ 2).re = RatFunc.C d at h
  rw [hProd] at h
  have hIm : y.im = 0 := by
    by_contra hi
    have hA₀ : radicand A ≠ 0 := by
      intro he
      exact square_ne_radicand A 0 (by simp [he])
    have hDeg := congrArg RatFunc.intDegree h
    rw [RatFunc.intDegree_mul (pow_ne_zero 2 hi) hA₀, pow_two,
      RatFunc.intDegree_mul hi hi, intDegree_radicand, RatFunc.intDegree_C] at hDeg
    omega
  exact QuadraticAlgebra.ext hr hIm

/-- The only zero-height anti-invariant generic points are killed by two. -/
theorem two_nsmul_eq_zero_of_height_zero (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (hA : A ≠ 0) (P : antiInvariant A) (h : height A P = 0) : (2 : ℕ) • P = 0 := by
  apply Subtype.ext
  obtain ⟨P, hP⟩ := P
  cases P with
  | zero => simp
  | some x y hp =>
    have h₂R : (2 : RatFunc K) ≠ 0 := by
      simpa only [map_ofNat] using (map_ne_zero (algebraMap K (RatFunc K))).mpr h₂
    have h₂L : (2 : Model A) ≠ 0 := by
      simpa only [map_ofNat] using (map_ne_zero (algebraMap K (Model A))).mpr h₂
    have h₃L : (3 : Model A) ≠ 0 := by
      simpa only [map_ofNat] using (map_ne_zero (algebraMap K (Model A))).mpr h₃
    have hAL := (map_ne_zero (algebraMap K (Model A))).mpr hA
    have hΔ := CubicThreeTorsionCard.shortCubic_discriminant_ne_zero h₂L h₃L hAL
    change rationalDegree x.re = 0 at h
    obtain ⟨c, hc⟩ := (RatFunc.eq_C_iff x.re).mpr (Nat.max_eq_zero_iff.mp h)
    obtain ⟨r, hX⟩ := exists_algebraMap_of_fixed h₂R (abscissa_fixed A hP)
    have hr : r = x.re := congrArg QuadraticAlgebra.re hX
    rw [hr, hc] at hX
    have hx : x = algebraMap K (Model A) c := hX.symm
    have hNeg := ordinate_antifixed A hP
    change star y = -y at hNeg
    have hRe : y.re = -y.re := by
      simpa only [QuadraticAlgebra.re_star, zero_mul, add_zero, QuadraticAlgebra.re_neg] using
        congrArg QuadraticAlgebra.re hNeg
    have hT : (2 : RatFunc K) * y.re = 0 := by linear_combination hRe
    have hPure := (mul_eq_zero.mp hT).resolve_left h₂R
    have hY : y ^ 2 = algebraMap K (Model A) (c ^ 3 + A) := by
      rw [map_add, map_pow, ← hx]
      exact (nonsingular_iff hΔ x y).mp hp
    have hy := pure_square_constant A hPure hY
    change (2 : ℕ) • (Affine.Point.some x y hp : Points A) = 0
    rw [two_nsmul]
    exact Affine.Point.add_of_Y_eq rfl (by simp [hy, Curve, CubicAffine, shortCubic, Affine.negY])

end

end ManuscriptAudit.CubicGenericZeroHeight

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicGenericZeroHeight.two_nsmul_eq_zero_of_height_zero
  let ax ← collectAxioms name
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  unless ax.all (allowed.contains ·) do
    throwError m!"{name} unexpected axioms {ax}"
  logInfo m!"{name} uses {ax}"
