import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicGenericAntiInvariant
import PrimalitySheafVerification.ManuscriptAudit.RationalProjectiveNormalization

/-! Canonical normalized polynomial abscissa pairs of the actual anti-invariant points. -/

namespace ManuscriptAudit.CubicGenericAbscissaPair

open Polynomial WeierstrassCurve CubicGenericFunctionField CubicGenericAntiInvariant
open RationalProjectiveNormalization

noncomputable section
open scoped Classical

variable {K : Type*} [Field K] (A : K)

/-- The homogeneous abscissa pair, reduced in K[X] for finite points and [1:0] at infinity. -/
def polynomialPair : Points A → Fin 2 → K[X]
  | .zero => ![1, 0]
  | .some x _ _ => ![x.re.num, x.re.denom]

/-- The native rational-coordinate pair is primitive after every geometric specialization. -/
theorem polynomialPair_rootFree (P : Points A) : RootFree (polynomialPair A P) := by
  intro x h
  let e := Polynomial.eval₂RingHom (algebraMap K (AlgebraicClosure K)) x
  cases P with
  | zero =>
    have hz := congrFun h 0
    change e 1 = 0 at hz
    rw [map_one] at hz
    exact one_ne_zero hz
  | some u v hP =>
    let r := u.re
    have hn : e r.num = 0 := congrFun h 0
    have hd : e r.denom = 0 := congrFun h 1
    obtain ⟨a, b, hBezout⟩ := r.isCoprime_num_denom
    have he := congrArg e hBezout
    rw [map_add, map_mul, map_mul, hn, hd, mul_zero, mul_zero, zero_add, map_one] at he
    exact zero_ne_one he

/-- Evaluate a polynomial coefficient in the actual generic field. -/
def coeffMap : K[X] →+* Model A :=
  (algebraMap (RatFunc K) (Model A)).comp (algebraMap K[X] (RatFunc K))

theorem coeffMap_C : ∀ k : K, coeffMap A (C k) = algebraMap K (Model A) k := by
  intro k
  change algebraMap (RatFunc K) (Model A) (algebraMap K[X] (RatFunc K) (C k)) = _
  rw [RatFunc.algebraMap_C]
  rfl

/-- The normalized pair gives the same homogeneous coordinates as Mathlib's actual xRep. -/
theorem polynomialPair_xRep (h₂ : (2 : K) ≠ 0) {P : Points A} (hP : P ∈ antiInvariant A) :
    ∃ c : Model A, c ≠ 0 ∧
      ∀ i, coeffMap A (polynomialPair A P i) = c * P.xRep i := by
  cases P with
  | zero =>
    refine ⟨1, one_ne_zero, ?_⟩
    intro i
    fin_cases i <;> simp [polynomialPair, Affine.Point.xRep]
  | some x y h =>
    have h₂' : (2 : RatFunc K) ≠ 0 := by
      simpa only [map_ofNat] using (map_ne_zero (algebraMap K (RatFunc K))).mpr h₂
    let e := algebraMap (RatFunc K) (Model A)
    let m := algebraMap K[X] (RatFunc K)
    let r := x.re
    have hx : e r = x := by
      obtain ⟨s, hs⟩ := exists_algebraMap_of_fixed h₂' (abscissa_fixed A hP)
      have hr : s = r := congrArg QuadraticAlgebra.re hs
      rwa [hr] at hs
    have hd : m r.denom ≠ 0 := RatFunc.algebraMap_ne_zero r.denom_ne_zero
    have hn : m r.num = m r.denom * r :=
      ((div_eq_iff hd).mp r.num_div_denom).trans (mul_comm _ _)
    have he : e (m r.num) = e (m r.denom) * x := by
      have h' := congrArg e hn
      rwa [map_mul, hx] at h'
    refine ⟨e (m r.denom), (map_ne_zero e).mpr hd, ?_⟩
    intro i
    fin_cases i
    · exact he
    · change e (m r.denom) = e (m r.denom) * 1
      rw [mul_one]

end

end ManuscriptAudit.CubicGenericAbscissaPair

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.CubicGenericAbscissaPair.polynomialPair_rootFree,
      ``ManuscriptAudit.CubicGenericAbscissaPair.coeffMap_C,
      ``ManuscriptAudit.CubicGenericAbscissaPair.polynomialPair_xRep] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
