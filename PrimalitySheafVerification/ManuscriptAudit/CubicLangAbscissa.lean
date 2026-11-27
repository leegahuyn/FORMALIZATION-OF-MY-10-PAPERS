import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import Mathlib.FieldTheory.RatFunc.Degree
import PrimalitySheafVerification.ManuscriptAudit.CubicFrobeniusDifferenceDegree
import PrimalitySheafVerification.ManuscriptAudit.RationalMapCofinite

/-! The reduced rational abscissa for Frobenius minus the identity has a cofinite comparison over the algebraic closure. -/

namespace ManuscriptAudit.CubicLangAbscissa

open Polynomial CubicFrobeniusDifferenceNumerator CubicFrobeniusDifferencePolynomial
open CubicFrobeniusDifferenceDegree CubicFrobeniusDifferenceGCD RationalMapCofinite

noncomputable section
open scoped Classical

variable (K L : Type*) [Field K] [Fintype K] [Field L] [Algebra K L]

/-- The normalized numerator has degree one more than the denominator. -/
theorem coordinate_intDegree {k : ℕ} (hq : Fintype.card K = 2 * k + 1) (hk : 0 < k) (A : K) :
    (coordinate K k A).intDegree = 1 := by
  have hN := numerator_natDegree hq hk A
  have hN₀ : numerator (Fintype.card K) k A ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hN
    omega
  rw [coordinate, RatFunc.intDegree_div (RatFunc.algebraMap_ne_zero hN₀)
    (RatFunc.algebraMap_ne_zero (denominator_ne_zero K)), RatFunc.intDegree_polynomial,
    RatFunc.intDegree_polynomial, hN, denominator_natDegree]
  push_cast
  omega

/-- All source abscissas where the secant formula has zero denominator are in this finite set. -/
def badSource : Finset L :=
  (((X : L[X]) ^ Fintype.card K - X)).roots.toFinset

theorem card_pow_ne_self_of_not_mem {x : L} (hx : x ∉ badSource K L) :
    x ^ Fintype.card K ≠ x := by
  intro h
  apply hx
  apply Multiset.mem_toFinset.mpr
  apply (mem_roots (FiniteField.X_pow_card_sub_X_ne_zero L Fintype.one_lt_card)).mpr
  change (((X : L[X]) ^ Fintype.card K - X)).eval x = 0
  simp only [eval_sub, eval_pow, eval_X, h, sub_self]

/-- Literal evaluations of the normalized and original rational functions agree away
from the exceptional secant source points. -/
theorem eval_coordinate_eq {k : ℕ} (A : K) {x : L}
    (hx : x ^ Fintype.card K ≠ x)
    (hD : ((coordinate K k A).denom.map (algebraMap K L)).eval x ≠ 0) :
    ((coordinate K k A).num.map (algebraMap K L)).eval x /
        ((coordinate K k A).denom.map (algebraMap K L)).eval x =
      (numerator (Fintype.card K) k (algebraMap K L A)).eval x /
        (x ^ Fintype.card K - x) ^ 2 := by
  let f := coordinate K k A
  let N := numerator (Fintype.card K) k A
  let D := denominator K
  let e := algebraMap K[X] (RatFunc K)
  have h := RatFunc.num_div_denom f
  change e f.num / e f.denom = e N / e D at h
  have he : f.num * D = N * f.denom := by
    apply RatFunc.algebraMap_injective K
    simp only [map_mul]
    exact (div_eq_div_iff (RatFunc.algebraMap_ne_zero f.denom_ne_zero)
      (RatFunc.algebraMap_ne_zero (denominator_ne_zero K))).mp h
  have heval := congrArg (fun w : K[X] => (w.map (algebraMap K L)).eval x) he
  simp only [Polynomial.map_mul, eval_mul] at heval
  have hDenom : (D.map (algebraMap K L)).eval x = (x ^ Fintype.card K - x) ^ 2 := by
    simp only [D, denominator, Polynomial.map_pow, Polynomial.map_sub, map_X,
      eval_pow, eval_sub, eval_X]
  have hNum : (N.map (algebraMap K L)).eval x =
      (numerator (Fintype.card K) k (algebraMap K L A)).eval x := by
    simp only [N, numerator, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      map_X, map_C, map_mul, map_ofNat, Polynomial.map_ofNat]
  apply (div_eq_div_iff hD (pow_ne_zero 2 (sub_ne_zero.mpr hx))).mpr
  simpa only [f, hDenom, hNum] using heval

def badTargets (k : ℕ) (A : K) : Finset L :=
  let f := coordinate K k A
  (badSource K L).image (fun x => (f.num.map (algebraMap K L)).eval x /
    (f.denom.map (algebraMap K L)).eval x)

/-- Every nonexceptional finite target is the secant abscissa of some permissible source. -/
theorem exists_secant_abscissa [IsAlgClosed L] {k : ℕ}
    (hq : Fintype.card K = 2 * k + 1) (hk : 0 < k) (A : K) {r : L}
    (hr : r ∉ badTargets K L k A) :
    ∃ x : L, x ^ Fintype.card K ≠ x ∧
      (numerator (Fintype.card K) k (algebraMap K L A)).eval x /
        (x ^ Fintype.card K - x) ^ 2 = r := by
  let e := algebraMap K L
  let f := coordinate K k A
  have hDegree := coordinate_intDegree K hq hk A
  change (f.num.natDegree : ℤ) - f.denom.natDegree = 1 at hDegree
  have hND : (f.denom.map e).natDegree < (f.num.map e).natDegree := by
    rw [natDegree_map_eq_of_injective e.injective, natDegree_map_eq_of_injective e.injective]
    omega
  have hCop : IsCoprime (f.num.map e) (f.denom.map e) :=
    f.isCoprime_num_denom.map (Polynomial.mapRingHom e)
  obtain ⟨x, hx, hD, hValue⟩ := exists_preimage_away hND hCop (badSource K L) hr
  have hx' := card_pow_ne_self_of_not_mem K L hx
  exact ⟨x, hx', (eval_coordinate_eq K L A hx' hD).symm.trans hValue⟩

end

end ManuscriptAudit.CubicLangAbscissa

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.CubicLangAbscissa.coordinate_intDegree,
      ``ManuscriptAudit.CubicLangAbscissa.card_pow_ne_self_of_not_mem,
      ``ManuscriptAudit.CubicLangAbscissa.eval_coordinate_eq,
      ``ManuscriptAudit.CubicLangAbscissa.exists_secant_abscissa] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
