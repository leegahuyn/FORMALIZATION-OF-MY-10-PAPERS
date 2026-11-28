import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspYChartAlgebra
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassInfinityChartAlgebra

/-! The literal Y=1 chart of a Weierstrass equation as an immersion in the plane. -/

namespace ManuscriptAudit.WeierstrassInfinityChartImmersion

open AlgebraicGeometry CategoryTheory HomogeneousLocalization Polynomial
open CuspYChartAlgebra (PlaneRing grading plane y z X_mem_one YChartRing yChartι
  fractionEvaluation fractionEvaluation_mk)

universe u

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} [Field K] (W : WeierstrassCurve.Affine K)

abbrev R := WeierstrassInfinityChartAlgebra.Ring W

def values (i : Fin 3) : R W :=
  if i = 0 then WeierstrassInfinityChartAlgebra.x W
  else if i = 1 then 1 else WeierstrassInfinityChartAlgebra.z W

def evaluation : PlaneRing K →ₐ[K] R W := MvPolynomial.aeval (values W)

private theorem eval_y_mul_one : evaluation W (y K) * 1 = 1 := by
  simp [evaluation, values, y]

def chartEvaluation : YChartRing K →+* R W :=
  fractionEvaluation K (evaluation W).toRingHom (y K) 1 (eval_y_mul_one W)

theorem chartEvaluation_mk (n : ℕ) (p : PlaneRing K) (hp : p ∈ grading K (n • 1)) :
    chartEvaluation W (Away.mk (grading K) (X_mem_one K 1) n p hp) = evaluation W p := by
  unfold chartEvaluation
  rw [fractionEvaluation_mk, one_pow, mul_one]
  rfl

def chartCoordinate (i : Fin 3) : YChartRing K :=
  Away.mk (grading K) (X_mem_one K 1) 1 (MvPolynomial.X i)
    (by simpa only [one_nsmul] using X_mem_one K i)

private def chartConstant (c : K) : YChartRing K :=
  Away.mk (grading K) (X_mem_one K 1) 0 (MvPolynomial.C c)
    (by
      rw [zero_nsmul]
      exact (MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_C (Fin 3) c))

theorem eval_chartCoordinate (i : Fin 3) : chartEvaluation W (chartCoordinate i) = values W i := by
  rw [chartCoordinate, chartEvaluation_mk]
  exact MvPolynomial.aeval_X _ _

private theorem eval_chartConstant (c : K) :
    chartEvaluation W (chartConstant c) = algebraMap K (R W) c := by
  rw [chartConstant, chartEvaluation_mk]
  exact MvPolynomial.aeval_C _ _

set_option maxHeartbeats 700000 in
theorem chartEvaluation_surjective : Function.Surjective (chartEvaluation W) := by
  let f := WeierstrassInfinityChartAlgebra.equation W
  let m : _ →+* R W := AdjoinRoot.mk f
  let g := m.comp (Polynomial.C : K[X] →+* _)
  have hX : ∃ a, chartEvaluation W a = g X :=
    ⟨chartCoordinate 0, by simp [eval_chartCoordinate, values, g, m, f,
      WeierstrassInfinityChartAlgebra.x]⟩
  have hZ : ∃ a, chartEvaluation W a = m X :=
    ⟨chartCoordinate 2, by simp [eval_chartCoordinate, values, m, f,
      WeierstrassInfinityChartAlgebra.z, AdjoinRoot.mk_X]⟩
  have hC (c : K) : ∃ a, chartEvaluation W a = g (Polynomial.C c) :=
    ⟨chartConstant c, eval_chartConstant W c⟩
  have coefficients (p : K[X]) : ∃ a, chartEvaluation W a = g p := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      obtain ⟨a, ha⟩ := hp
      obtain ⟨b, hb⟩ := hq
      exact ⟨a + b, by rw [map_add, map_add, ha, hb]⟩
    | monomial n c =>
      obtain ⟨a, ha⟩ := hC c
      obtain ⟨b, hb⟩ := hX
      refine ⟨a * b ^ n, ?_⟩
      rw [map_mul, map_pow, ha, hb, ← C_mul_X_pow_eq_monomial, map_mul, map_pow]
  intro r
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective f r
  change ∃ a, chartEvaluation W a = m p
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    exact ⟨a + b, by rw [map_add, map_add, ha, hb]⟩
  | monomial n c =>
    obtain ⟨a, ha⟩ := coefficients c
    obtain ⟨b, hb⟩ := hZ
    refine ⟨a * b ^ n, ?_⟩
    rw [map_mul, map_pow, ha, hb, ← C_mul_X_pow_eq_monomial, map_mul, map_pow] <;> rfl

abbrev chartScheme : Scheme.{u} := Spec (CommRingCat.of (R W))

def toYChart : chartScheme W ⟶ Spec (CommRingCat.of (YChartRing K)) :=
  Spec.map (CommRingCat.ofHom (chartEvaluation W))

theorem toYChart_isClosedImmersion : IsClosedImmersion (toYChart W) :=
  IsClosedImmersion.spec_of_surjective _ (chartEvaluation_surjective W)

def inPlane : chartScheme W ⟶ plane K := toYChart W ≫ yChartι K

instance inPlane_isImmersion : IsImmersion (inPlane W) := by
  letI := toYChart_isClosedImmersion W
  unfold inPlane
  infer_instance

instance inPlane_quasiCompact : QuasiCompact (inPlane W) := quasiCompact_of_compactSpace _

theorem inPlane_preimage_z :
    (inPlane W) ⁻¹ᵁ Proj.basicOpen (grading K) (z K) =
      PrimeSpectrum.basicOpen (WeierstrassInfinityChartAlgebra.z W) := by
  unfold inPlane toYChart
  rw [Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen (𝒜 := grading K) (X_mem_one K 1) (by decide)
      (X_mem_one K 2) (by decide), SpecMap_preimage_basicOpen]
  have he :
      chartEvaluation W (Away.isLocalizationElem (X_mem_one K 1) (X_mem_one K 2)) =
        WeierstrassInfinityChartAlgebra.z W := by
    unfold Away.isLocalizationElem
    rw [chartEvaluation_mk, pow_one]
    simp [evaluation, values]
  change PrimeSpectrum.basicOpen
      (chartEvaluation W (Away.isLocalizationElem (X_mem_one K 1) (X_mem_one K 2))) = _
  rw [he]

end

end ManuscriptAudit.WeierstrassInfinityChartImmersion

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassInfinityChartImmersion.chartEvaluation_mk,
      ``ManuscriptAudit.WeierstrassInfinityChartImmersion.chartEvaluation_surjective,
      ``ManuscriptAudit.WeierstrassInfinityChartImmersion.toYChart_isClosedImmersion,
      ``ManuscriptAudit.WeierstrassInfinityChartImmersion.inPlane_preimage_z] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
