import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Jacobson.Ring

/-!
# Closed points of the geometric affine Weierstrass curve

Zariski's lemma and algebraic closedness identify each closed point's
residue field with the base. The two affine coordinates then recover
its maximal ideal, which is invertible for an elliptic equation.
-/

namespace ManuscriptAudit.WeierstrassAffineClosedPoints

open Polynomial WeierstrassCurve.Affine
open scoped Polynomial.Bivariate nonZeroDivisors

noncomputable section

variable {K : Type*} [Field K] [IsAlgClosed K] (W : WeierstrassCurve.Affine K)

/-- The actual residue field of any geometric closed point is the base field. -/
def residueEquiv (I : Ideal W.CoordinateRing) [I.IsMaximal] :
    K ≃ₐ[K] W.CoordinateRing ⧸ I := by
  letI : Field (W.CoordinateRing ⧸ I) := Ideal.Quotient.field I
  letI : Algebra.FiniteType K W.CoordinateRing :=
    inferInstanceAs (Algebra.FiniteType K (AdjoinRoot W.polynomial))
  letI : Module.Finite K (W.CoordinateRing ⧸ I) :=
    finite_of_finite_type_of_isJacobsonRing K (W.CoordinateRing ⧸ I)
  exact AlgEquiv.ofBijective (Algebra.ofId K (W.CoordinateRing ⧸ I))
    IsAlgClosed.algebraMap_bijective_of_isIntegral

/-- Each maximal ideal of the literal affine coordinate ring is the ideal
of a rational affine point over the algebraically closed base. -/
theorem maximalIdeal_is_point (I : Ideal W.CoordinateRing) (hI : I.IsMaximal) :
    ∃ x y : K, W.Equation x y ∧ I = CoordinateRing.XYIdeal W x (C y) := by
  letI : I.IsMaximal := hI
  let e := residueEquiv W I
  let f : W.CoordinateRing →ₐ[K] K :=
    e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ K I)
  let g : K[X][Y] →ₐ[K] K := f.comp ((AdjoinRoot.mkₐ W.polynomial).restrictScalars K)
  let xy := (Polynomial.aevalAevalEquiv K K).symm g
  let x := xy.1
  let y := xy.2
  have hEval : Polynomial.aevalAeval x y = g :=
    (Polynomial.aevalAevalEquiv K K).apply_symm_apply g
  have hW : g W.polynomial = 0 := by
    change f (AdjoinRoot.mk W.polynomial W.polynomial) = 0
    rw [AdjoinRoot.mk_self, map_zero]
  have he : W.Equation x y := by
    change W.polynomial.evalEval x y = 0
    rw [← Polynomial.coe_aevalAeval_eq_evalEval, hEval]
    exact hW
  have hMem (z : W.CoordinateRing) (hz : f z = 0) : z ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply e.symm.injective
    calc
      e.symm (Ideal.Quotient.mk I z) = f z := rfl
      _ = 0 := hz
      _ = e.symm 0 := (map_zero e.symm).symm
  let J := CoordinateRing.XYIdeal W x (C y)
  have hJle : J ≤ I := by
    change Ideal.span {CoordinateRing.XClass W x, CoordinateRing.YClass W (C y)} ≤ I
    rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    constructor
    · apply hMem
      change g (C (X - C x)) = 0
      rw [← hEval, Polynomial.aevalAeval_C]
      simp
    · apply hMem
      change g (Y - C (C y)) = 0
      rw [← hEval, map_sub, Polynomial.aevalAeval_Y, Polynomial.aevalAeval_C]
      simp
  let eJ : (W.CoordinateRing ⧸ J) ≃ₐ[K] K := CoordinateRing.quotientXYIdealEquiv he
  let fJ : W.CoordinateRing →ₐ[K] K := eJ.toAlgHom.comp (Ideal.Quotient.mkₐ K J)
  have hJker : RingHom.ker fJ.toRingHom = J := by
    ext z
    change eJ (Ideal.Quotient.mk J z) = 0 ↔ z ∈ J
    constructor
    · intro hz
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      apply eJ.injective
      exact hz.trans (map_zero eJ).symm
    · intro hz
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hz, map_zero]
  have hJmax : J.IsMaximal := by
    rw [← hJker]
    exact RingHom.ker_isMaximal_of_surjective fJ.toRingHom
      (eJ.surjective.comp (Ideal.Quotient.mkₐ_surjective K J))
  exact ⟨x, y, he, (hJmax.eq_of_le hI.ne_top hJle).symm⟩

/-- Every maximal ideal of a smooth geometric Weierstrass affine chart is
an invertible fractional ideal in the actual function field. -/
theorem maximalIdeal_is_unit [W.IsElliptic] (I : Ideal W.CoordinateRing) (hI : I.IsMaximal) :
    IsUnit (I : FractionalIdeal W.CoordinateRing⁰ W.FunctionField) := by
  obtain ⟨x, y, hxy, rfl⟩ := maximalIdeal_is_point W I hI
  have hn : W.Nonsingular x y := (equation_iff_nonsingular (W := W)).mp hxy
  exact ⟨CoordinateRing.XYIdeal' hn, CoordinateRing.XYIdeal'_eq hn⟩

end

end ManuscriptAudit.WeierstrassAffineClosedPoints

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassAffineClosedPoints.residueEquiv,
      ``ManuscriptAudit.WeierstrassAffineClosedPoints.maximalIdeal_is_point,
      ``ManuscriptAudit.WeierstrassAffineClosedPoints.maximalIdeal_is_unit] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
