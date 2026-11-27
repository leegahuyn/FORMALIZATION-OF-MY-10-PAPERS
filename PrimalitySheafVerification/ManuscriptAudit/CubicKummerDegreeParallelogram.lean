import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import PrimalitySheafVerification.ManuscriptAudit.CubicKummerSymmetricHeight
import PrimalitySheafVerification.ManuscriptAudit.RationalProjectiveNormalization

/-! The centered cubic's homogeneous Kummer equality gives the exact rational degree parallelogram. -/

namespace ManuscriptAudit.CubicKummerDegreeParallelogram

open Polynomial CubicKummerHeight CubicKummerQuadratic CubicKummerSymmetricHeight
open RationalProjectiveNormalization

variable {K : Type*} [Field K]

private theorem rootFree_ne_zero {ι : Type*} {v : ι → K[X]} (hv : RootFree v) : v ≠ 0 := by
  intro h
  apply hv 0
  rw [h]
  funext i
  simp

theorem rootFree_symmetric {a b : Fin 2 → K[X]} (ha : RootFree a) (hb : RootFree b) :
    RootFree (symmetric a b) := by
  intro x
  let f := Polynomial.eval₂RingHom (algebraMap K (AlgebraicClosure K)) x
  have hEq := map_symmetric f a b
  change symmetric (fun i => (a i).eval₂ (algebraMap K (AlgebraicClosure K)) x)
    (fun i => (b i).eval₂ (algebraMap K (AlgebraicClosure K)) x) =
    (fun i => (symmetric a b i).eval₂ (algebraMap K (AlgebraicClosure K)) x) at hEq
  rw [← hEq]
  exact symmetric_ne_zero (ha x) (hb x)

/-- Any actual projective Kummer equality, even over a larger function field, has the
precise degree consequence on normalized K(x)-coordinates. -/
theorem degree_parallelogram {L : Type*} [Field L] [Algebra (RatFunc K) L]
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) {A : K} (hA : A ≠ 0)
    {a b p m : Fin 2 → K[X]} (ha : RootFree a) (hb : RootFree b)
    (hp : RootFree p) (hm : RootFree m) {c : L} (hc : c ≠ 0)
    (hEq : ∀ i, algebraMap (RatFunc K) L
      (algebraMap K[X] (RatFunc K) (forms (C A) (symmetric a b) i)) =
      c * algebraMap (RatFunc K) L (algebraMap K[X] (RatFunc K) (symmetric p m i))) :
    pairHeight p + pairHeight m = 2 * pairHeight a + 2 * pairHeight b := by
  have hSym := rootFree_symmetric ha hb
  have hLeft : RootFree (forms (C A) (symmetric a b)) :=
    fun x => no_common_root_forms h₂ h₃ hA (hSym x)
  have hRight := rootFree_symmetric hp hm
  have hDeg := natDegree_eq_of_projective_extension hLeft hRight hc hEq
  have hH : height (forms (C A) (symmetric a b)) = height (symmetric p m) := by
    unfold height
    rw [hDeg 0, hDeg 1, hDeg 2]
  rw [height_forms h₂ h₃ hA (rootFree_ne_zero hSym),
    height_symmetric (rootFree_ne_zero ha) (rootFree_ne_zero hb),
    height_symmetric (rootFree_ne_zero hp) (rootFree_ne_zero hm)] at hH
  omega

end ManuscriptAudit.CubicKummerDegreeParallelogram

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.CubicKummerDegreeParallelogram.rootFree_symmetric,
      ``ManuscriptAudit.CubicKummerDegreeParallelogram.degree_parallelogram] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
