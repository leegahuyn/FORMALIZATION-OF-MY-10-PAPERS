import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Polynomial.Derivation
import PrimalitySheafVerification.ManuscriptAudit.CuspDelta
import PrimalitySheafVerification.ManuscriptAudit.CuspPlaneSmoothness
import PrimalitySheafVerification.Spt5

/-!
# First cotangent homology of the affine cusp

The quotient \(K[X,Y]/(Y^2-X^3)\) has zero first cotangent homology over
\(K\) when \(2\) is nonzero. The \(Y\)-derivation pairs with the actual
conormal differential and detects it by multiplication by \(2Y\).
This computes the first cotangent homology used in Paper 2.
-/

namespace ManuscriptAudit.CuspCotangent

open Algebra Polynomial
open scoped nonZeroDivisors

noncomputable section

variable (K : Type*) [Field K]

private abbrev P := Polynomial (Polynomial K)

/-- The actual affine cusp coordinate quotient. -/
abbrev CuspRing := AdjoinRoot (CuspDelta.cuspPlaneEquation K)

private abbrev cuspProjection : P K →ₐ[K] CuspRing K :=
  (AdjoinRoot.mkₐ (CuspDelta.cuspPlaneEquation K)).restrictScalars K

private abbrev E : Algebra.Extension K (CuspRing K) :=
  Algebra.Extension.ofSurjective (cuspProjection K) (by
    intro x
    obtain ⟨g, hg⟩ := AdjoinRoot.mk_surjective (g := CuspDelta.cuspPlaneEquation K) x
    exact ⟨g, hg⟩)

private theorem E_ker : (E K).ker = Ideal.span {CuspDelta.cuspPlaneEquation K} := by
  ext g
  change AdjoinRoot.mk (CuspDelta.cuspPlaneEquation K) g = 0 ↔
    g ∈ Ideal.span {CuspDelta.cuspPlaneEquation K}
  exact (AdjoinRoot.mk_eq_zero (f := CuspDelta.cuspPlaneEquation K) (g := (show P K from g))).trans
    Ideal.mem_span_singleton.symm

private theorem monic_equation : (CuspDelta.cuspPlaneEquation K).Monic :=
  Polynomial.monic_X_pow_sub_C ((Polynomial.X : Polynomial K) ^ 3) (n := 2) (by decide)

private def relationInKer : (E K).ker :=
  ⟨CuspDelta.cuspPlaneEquation K, by
    rw [E_ker]
    exact Ideal.mem_span_singleton_self _⟩

private theorem equation_regular : CuspDelta.cuspPlaneEquation K ∈ ((E K).Ring)⁰ := by
  change CuspDelta.cuspPlaneEquation K ∈ (P K)⁰
  exact mem_nonZeroDivisors_of_ne_zero (monic_equation K).ne_zero

private def derivativePairing : (E K).CotangentSpace →ₗ[CuspRing K] CuspRing K :=
  let D : Derivation K (E K).Ring (E K).Ring :=
    (Polynomial.derivative' (R := Polynomial K)).restrictScalars K
  ((Algebra.linearMap (E K).Ring (CuspRing K)).comp
    D.liftKaehlerDifferential).liftBaseChange (CuspRing K)

private theorem derivativePairing_of_relation :
    derivativePairing K ((E K).cotangentComplex
      (Algebra.Extension.Cotangent.mk (relationInKer K))) =
      (2 : CuspRing K) * AdjoinRoot.root (CuspDelta.cuspPlaneEquation K) := by
  rw [Algebra.Extension.cotangentComplex_mk]
  unfold derivativePairing
  rw [LinearMap.liftBaseChange_one_tmul, LinearMap.comp_apply]
  let D : Derivation K (E K).Ring (E K).Ring :=
    (Polynomial.derivative' (R := Polynomial K)).restrictScalars K
  let x : (E K).Ring := (relationInKer K : (E K).ker)
  have hEval := D.liftKaehlerDifferential_comp_D x
  refine (congrArg (Algebra.linearMap (E K).Ring (CuspRing K)) hEval).trans ?_
  change AdjoinRoot.mk (CuspDelta.cuspPlaneEquation K)
    (Polynomial.derivative (CuspDelta.cuspPlaneEquation K)) =
      (2 : CuspRing K) * AdjoinRoot.root (CuspDelta.cuspPlaneEquation K)
  have hd : Polynomial.derivative (CuspDelta.cuspPlaneEquation K) =
      Polynomial.C (2 : Polynomial K) * (Polynomial.X : P K) := by
    simp only [CuspDelta.cuspPlaneEquation, Polynomial.derivative_sub,
      Polynomial.derivative_X_pow, Polynomial.derivative_C, sub_zero]
    change Polynomial.C (2 : Polynomial K) * (Polynomial.X : P K) ^ 1 = _
    rw [pow_one]
  have hcoef : AdjoinRoot.mk (CuspDelta.cuspPlaneEquation K) (Polynomial.C (2 : Polynomial K)) =
      (2 : CuspRing K) := by
    calc
      _ = AdjoinRoot.mk (CuspDelta.cuspPlaneEquation K) (2 : P K) :=
        congrArg (AdjoinRoot.mk (CuspDelta.cuspPlaneEquation K))
          (map_ofNat (Polynomial.C : Polynomial K →+* P K) 2)
      _ = _ := map_ofNat (AdjoinRoot.mk (CuspDelta.cuspPlaneEquation K)) 2
  rw [hd, map_mul, AdjoinRoot.mk_X, hcoef]

private theorem root_ne_zero :
    AdjoinRoot.root (CuspDelta.cuspPlaneEquation K) ≠ 0 := by
  change AdjoinRoot.mk (CuspDelta.cuspPlaneEquation K) (Polynomial.X : P K) ≠ 0
  exact AdjoinRoot.mk_ne_zero_of_natDegree_lt (monic_equation K) Polynomial.X_ne_zero
    (by
      rw [Polynomial.natDegree_X]
      change 1 < (Polynomial.X ^ 2 - Polynomial.C ((Polynomial.X : Polynomial K) ^ 3)).natDegree
      simpa only [Polynomial.natDegree_X_pow_sub_C] using (by decide : (1 : ℕ) < 2))

/-- The actual first cotangent homology of the affine cusp vanishes
when the characteristic is different from two. -/
theorem paper2_cusp_h1Cotangent_subsingleton (h2 : (2 : K) ≠ 0) :
    Subsingleton (Algebra.H1Cotangent K (CuspRing K)) := by
  let iso := CuspDelta.paper2_cusp_coordinate_presentation K
  letI : IsDomain (CuspRing K) := Function.Injective.isDomain iso.toRingEquiv.toRingHom iso.injective
  letI : Algebra.FormallySmooth K (E K).Ring := by
    change Algebra.FormallySmooth K (P K)
    exact Algebra.FormallySmooth.comp K (Polynomial K) (P K)
  let e := Spt5.extCotangentEquiv (E K) (CuspDelta.cuspPlaneEquation K)
    (equation_regular K) (E_ker K)
  have hgen : e 1 = Algebra.Extension.Cotangent.mk (relationInKer K) :=
    Spt5.extCotangentEquiv_one (E K) (CuspDelta.cuspPlaneEquation K)
      (equation_regular K) (E_ker K)
  have hpair : derivativePairing K ((E K).cotangentComplex (e 1)) =
      (2 : CuspRing K) * AdjoinRoot.root (CuspDelta.cuspPlaneEquation K) := by
    rw [hgen, derivativePairing_of_relation]
  have h2S : (2 : CuspRing K) ≠ 0 := by
    have h := (algebraMap K (CuspRing K)).injective.ne h2
    simpa only [map_ofNat, map_zero] using h
  apply ((E K).cotangentComplex_injective_iff).mp
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨s, rfl⟩ := e.surjective z
  have he : e s = s • e 1 := by
    rw [← map_smul, smul_eq_mul, mul_one]
  have hs : s * ((2 : CuspRing K) * AdjoinRoot.root (CuspDelta.cuspPlaneEquation K)) = 0 := by
    simpa only [he, map_smul, hpair, smul_eq_mul, map_zero] using
      congrArg (derivativePairing K) hz
  have hsz : s = 0 := (mul_eq_zero.mp hs).resolve_right
    (mul_ne_zero h2S (root_ne_zero K))
  rw [hsz, map_zero]

/-- The integral affine cusp is singular despite vanishing first cotangent homology. -/
theorem paper2_integral_cusp_h1_cotangent_vanishing_and_singular (h2 : (2 : K) ≠ 0) :
    Subsingleton (Algebra.H1Cotangent K (AdjoinRoot (CuspDelta.cuspPlaneEquation K))) ∧
      ¬ Algebra.Smooth K (AdjoinRoot (CuspDelta.cuspPlaneEquation K)) :=
  ⟨paper2_cusp_h1Cotangent_subsingleton K h2, CuspPlaneSmoothness.cuspPlane_not_smooth K⟩

end

end ManuscriptAudit.CuspCotangent

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.CuspCotangent.paper2_cusp_h1Cotangent_subsingleton
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
