import Lean.Util.CollectAxioms
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.NodalAffinePresentation

/-! The integral affine node y²=x²(x+1) fails the actual infinitesimal
lifting criterion. The witness sends x to 0 and y to ε modulo ε²,
and lifts into K[ε]/ε³ would retain the nonzero term ε². -/

namespace ManuscriptAudit.NodalAffineSingular

open Polynomial NodalConductor NodalAffinePresentation

noncomputable section

variable (K : Type*) [Field K]

private abbrev A := coordinates K
private abbrev C := AdjoinRoot (equation K)

private theorem node_relation : nodeY K ^ 2 = nodeX K ^ 2 * (nodeX K + 1) := by
  apply Subtype.ext
  change y K ^ 2 = x K ^ 2 * (x K + 1)
  unfold y x
  ring

variable {D : Type*} [CommRing D] [Algebra K D]

private theorem evaluate_equation (a b : D) (h : b ^ 2 = a ^ 2 * (a + 1)) :
    (equation K).eval₂ (Polynomial.aeval a : Polynomial K →ₐ[K] D).toRingHom b = 0 := by
  have hx : (Polynomial.aeval a : Polynomial K →ₐ[K] D).toRingHom Polynomial.X = a :=
    Polynomial.aeval_X (R := K) a
  simpa only [equation, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C, map_mul, map_pow, map_add, map_one, hx]
    using sub_eq_zero.mpr h

private def evalPresentation (a b : D) (h : b ^ 2 = a ^ 2 * (a + 1)) : C K →ₐ[K] D :=
  AdjoinRoot.liftAlgHom (equation K) (Polynomial.aeval a) b (evaluate_equation K a b h)

private def evaluate (a b : D) (h : b ^ 2 = a ^ 2 * (a + 1)) : A K →ₐ[K] D :=
  (evalPresentation K a b h).comp (coordinateEquiv K).symm.toAlgHom

private theorem evaluate_x (a b : D) (h : b ^ 2 = a ^ 2 * (a + 1)) :
    evaluate K a b h (nodeX K) = a := by
  have hx : coordinateEquiv K (AdjoinRoot.of (equation K) Polynomial.X) = nodeX K := by
    change parameter K (AdjoinRoot.of (equation K) Polynomial.X) = _
    rw [parameter_base]
    exact Polynomial.aeval_X (R := K) (nodeX K)
  change evalPresentation K a b h ((coordinateEquiv K).symm (nodeX K)) = a
  rw [← hx, AlgEquiv.symm_apply_apply]
  exact (AdjoinRoot.liftAlgHom_of (equation K) (Polynomial.aeval a) b
    (evaluate_equation K a b h) Polynomial.X).trans (Polynomial.aeval_X (R := K) a)

private theorem evaluate_y (a b : D) (h : b ^ 2 = a ^ 2 * (a + 1)) :
    evaluate K a b h (nodeY K) = b := by
  have hy : coordinateEquiv K (AdjoinRoot.root (equation K)) = nodeY K :=
    parameter_root K
  change evalPresentation K a b h ((coordinateEquiv K).symm (nodeY K)) = b
  rw [← hy, AlgEquiv.symm_apply_apply]
  exact AdjoinRoot.liftAlgHom_root (equation K) (Polynomial.aeval a) b (evaluate_equation K a b h)

set_option maxHeartbeats 1200000 in
private theorem not_formallySmooth_from_truncation {B : Type*} [CommRing B] [Algebra K B]
    (t : B) (ht₃ : t ^ 3 = 0) (ht₂ : t ^ 2 ≠ 0) : ¬ Algebra.FormallySmooth K (A K) := by
  intro hs
  letI : Algebra.FormallySmooth K (A K) := hs
  let J : Ideal B := Ideal.span {t ^ 2}
  let q : B →ₐ[K] B ⧸ J := Ideal.Quotient.mkₐ K J
  have hJ : J ^ 2 = ⊥ := by
    have hnil : (t ^ 2) ^ 2 = 0 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by decide, pow_add, ht₃, zero_mul]
    change (Ideal.span ({t ^ 2} : Set B)) ^ 2 = ⊥
    rw [Ideal.span_singleton_pow, hnil]
    simp
  have hAnn {r : B} (hr : r ∈ J) : t * r = 0 := by
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp hr
    rw [hd]
    calc
      _ = (t ^ 2 * t) * d := by ac_rfl
      _ = 0 := by rw [← pow_succ t 2, ht₃, zero_mul]
  have hSq {r : B} (hr : r ∈ J) : r ^ 2 = 0 := by
    have hm : r * r ∈ J * J := Ideal.mul_mem_mul hr hr
    rw [← pow_two J, hJ, Ideal.mem_bot] at hm
    simpa only [pow_two] using hm
  have hqt : (q t) ^ 2 = 0 := by
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hred : (q t) ^ 2 = (0 : B ⧸ J) ^ 2 * (0 + 1) := by simp [hqt]
  let φ : A K →ₐ[K] B ⧸ J := evaluate K 0 (q t) hred
  obtain ⟨l, hl⟩ := Algebra.FormallySmooth.comp_surjective K (A K) J hJ φ
  have hx : q (l (nodeX K)) = 0 :=
    (AlgHom.congr_fun hl _).trans (evaluate_x K 0 (q t) hred)
  have hy : q (l (nodeY K)) = q t :=
    (AlgHom.congr_fun hl _).trans (evaluate_y K 0 (q t) hred)
  have hxJ : l (nodeX K) ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp hx
  let d := l (nodeY K) - t
  have hd : d ∈ J := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q d = 0
    simp only [d, map_sub, hy, sub_self]
  have hylift : l (nodeY K) ^ 2 = t ^ 2 := by
    calc
      _ = (t + d) ^ 2 := by unfold d; ring
      _ = t ^ 2 + 2 * (t * d) + d ^ 2 := by ring
      _ = t ^ 2 := by rw [hAnn hd, hSq hd, mul_zero, add_zero, add_zero]
  have he := congrArg l (node_relation K)
  rw [map_mul, map_pow, map_pow, hSq hxJ, zero_mul, hylift] at he
  exact ht₂ he

/-- The actual integral affine nodal algebra is not formally smooth over K. -/
theorem affineNode_not_formallySmooth : ¬ Algebra.FormallySmooth K (coordinates K) := by
  let I : Ideal (Polynomial K) := Ideal.span {(Polynomial.X : Polynomial K) ^ 3}
  let t : Polynomial K ⧸ I := Ideal.Quotient.mk I Polynomial.X
  have ht₃ : t ^ 3 = 0 := by
    change (Ideal.Quotient.mk I (Polynomial.X : Polynomial K)) ^ 3 = 0
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have ht₂ : t ^ 2 ≠ 0 := by
    intro h
    change (Ideal.Quotient.mk I (Polynomial.X : Polynomial K)) ^ 2 = 0 at h
    rw [← map_pow] at h
    have hdiv : (Polynomial.X : Polynomial K) ^ 3 ∣ Polynomial.X ^ 2 :=
      Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp h)
    have hc := (Polynomial.X_pow_dvd_iff.mp hdiv) 2 (by decide)
    exact one_ne_zero (by simpa using hc)
  exact not_formallySmooth_from_truncation K t ht₃ ht₂

theorem affineNode_not_smooth : ¬ Algebra.Smooth K (coordinates K) :=
  fun h => affineNode_not_formallySmooth K h.formallySmooth

end
end ManuscriptAudit.NodalAffineSingular

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalAffineSingular.affineNode_not_formallySmooth,
      ``ManuscriptAudit.NodalAffineSingular.affineNode_not_smooth] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
