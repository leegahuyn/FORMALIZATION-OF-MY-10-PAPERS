import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspYChartAlgebra
import PrimalitySheafVerification.ManuscriptAudit.NodalYChartAlgebra

/-!
# The nodal equation in the Y=1 affine chart of the actual projective plane

The degree-zero evaluation sends X/Y and Z/Y to x and z in the
coordinate ring with relation z=x²(x+z). The map is surjective, so
the resulting morphism into the native Y≠0 affine chart is a closed
immersion. The inverse of 1−x² is 1+x²+xz on this chart, and the
intersection with Z≠0 is D(x).
-/

namespace ManuscriptAudit.NodalYChartImmersion

open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open CuspYChartAlgebra
  (PlaneRing grading plane y z X_mem_one YChartRing yChartι fractionEvaluation fractionEvaluation_mk)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable (K : Type u) [Field K]

def yEquation : Polynomial (Polynomial K) :=
  Polynomial.C ((1 : Polynomial K) - Polynomial.X ^ 2) * Polynomial.X -
    Polynomial.C ((Polynomial.X : Polynomial K) ^ 3)

theorem yEquation_printed :
    yEquation K = (Polynomial.X : Polynomial (Polynomial K)) -
      Polynomial.C ((Polynomial.X : Polynomial K) ^ 2) *
        (Polynomial.C (Polynomial.X : Polynomial K) + Polynomial.X) :=
  NodalYChartAlgebra.nodalYEquation K

abbrev yCoordinateRing := AdjoinRoot (yEquation K)

def coordinateEquiv :
    yCoordinateRing K ≃ₐ[Polynomial K]
      Localization.Away ((1 : Polynomial K) - Polynomial.X ^ 2) :=
  NodalYChartAlgebra.nodalYChartEquiv K

def xCoeff : yCoordinateRing K :=
  algebraMap (Polynomial K) (yCoordinateRing K) Polynomial.X

def zCoeff : yCoordinateRing K := AdjoinRoot.root (yEquation K)

def yValues (i : Fin 3) : yCoordinateRing K :=
  if i = 0 then xCoeff K else if i = 1 then 1 else zCoeff K

def evalYPolynomial : PlaneRing K →ₐ[K] yCoordinateRing K :=
  MvPolynomial.aeval (yValues K)

private theorem evalY_y_mul_one : evalYPolynomial K (y K) * 1 = 1 := by
  simp [evalYPolynomial, yValues, y]

def evalYChart : YChartRing K →+* yCoordinateRing K :=
  fractionEvaluation K (evalYPolynomial K).toRingHom (y K) 1 (evalY_y_mul_one K)

theorem evalYChart_mk (n : ℕ) (p : PlaneRing K) (hp : p ∈ grading K (n • 1)) :
    evalYChart K (Away.mk (grading K) (X_mem_one K 1) n p hp) = evalYPolynomial K p := by
  unfold evalYChart
  rw [fractionEvaluation_mk, one_pow, mul_one]
  rfl

/-- The fraction Xi/Y in the ambient affine projective-plane chart. -/
abbrev chartCoordinate (i : Fin 3) : YChartRing K :=
  Away.isLocalizationElem (X_mem_one K 1) (X_mem_one K i)

theorem evalYChart_coordinate (i : Fin 3) :
    evalYChart K (chartCoordinate K i) = yValues K i := by
  unfold chartCoordinate Away.isLocalizationElem
  rw [evalYChart_mk, pow_one]
  exact MvPolynomial.aeval_X (yValues K) i

theorem evalYChart_X : evalYChart K (chartCoordinate K 0) = xCoeff K := by
  rw [evalYChart_coordinate]
  simp [yValues]

theorem evalYChart_Z : evalYChart K (chartCoordinate K 2) = zCoeff K := by
  rw [evalYChart_coordinate]
  simp [yValues]

private def chartConstant (c : K) : YChartRing K :=
  Away.mk (grading K) (X_mem_one K 1) 0 (MvPolynomial.C c)
    (by simpa only [zero_nsmul] using
      (MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_C (Fin 3) c))

private theorem evalYChart_constant (c : K) :
    evalYChart K (chartConstant K c) = algebraMap K (yCoordinateRing K) c := by
  rw [chartConstant, evalYChart_mk]
  simp [evalYPolynomial]

private theorem evalYChart_polynomial (p : Polynomial K) :
    ∃ q : YChartRing K, evalYChart K q = algebraMap (Polynomial K) (yCoordinateRing K) p := by
  induction p using Polynomial.induction_on' with
  | add a b ha hb =>
    obtain ⟨f, hf⟩ := ha
    obtain ⟨g, hg⟩ := hb
    exact ⟨f + g, by rw [map_add, hf, hg, map_add]⟩
  | monomial n c =>
    have hc : algebraMap (Polynomial K) (yCoordinateRing K) (Polynomial.C c) =
        algebraMap K (yCoordinateRing K) c := by
      rw [Polynomial.C_eq_algebraMap]
      exact (IsScalarTower.algebraMap_apply K (Polynomial K) (yCoordinateRing K) c).symm
    refine ⟨chartConstant K c * chartCoordinate K 0 ^ n, ?_⟩
    rw [map_mul, map_pow, evalYChart_constant, evalYChart_X,
      ← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, hc] <;> rfl

theorem evalYChart_surjective : Function.Surjective (evalYChart K) := by
  intro q
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective (g := yEquation K) q
  induction p using Polynomial.induction_on' with
  | add a b ha hb =>
    obtain ⟨f, hf⟩ := ha
    obtain ⟨g, hg⟩ := hb
    exact ⟨f + g, by rw [map_add, hf, hg, map_add]⟩
  | monomial n c =>
    obtain ⟨f, hf⟩ := evalYChart_polynomial K c
    refine ⟨f * chartCoordinate K 2 ^ n, ?_⟩
    rw [map_mul, map_pow, hf, evalYChart_Z, ← Polynomial.C_mul_X_pow_eq_monomial,
      map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X] <;> rfl

abbrev nodeYChart : Scheme.{u} := Spec (CommRingCat.of (yCoordinateRing K))

/-- The actual affine nodal subscheme of the native Y≠0 chart. -/
def nodeToYChart : nodeYChart K ⟶ Spec (CommRingCat.of (YChartRing K)) :=
  Spec.map (CommRingCat.ofHom (evalYChart K))

instance nodeToYChart_closed : IsClosedImmersion (nodeToYChart K) :=
  IsClosedImmersion.spec_of_surjective _ (evalYChart_surjective K)

def nodeYInPlane : nodeYChart K ⟶ plane K := nodeToYChart K ≫ yChartι K

instance nodeYInPlane_isImmersion : IsImmersion (nodeYInPlane K) := by
  unfold nodeYInPlane
  infer_instance

theorem yRing_cubic_relation :
    zCoeff K - xCoeff K ^ 2 * (xCoeff K + zCoeff K) = 0 := by
  have h : AdjoinRoot.mk (yEquation K)
      ((Polynomial.X : Polynomial (Polynomial K)) -
        Polynomial.C ((Polynomial.X : Polynomial K) ^ 2) *
          (Polynomial.C (Polynomial.X : Polynomial K) + Polynomial.X)) = 0 := by
    rw [← yEquation_printed]
    exact AdjoinRoot.mk_self
  rw [map_sub, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C,
    map_add, AdjoinRoot.mk_C, AdjoinRoot.mk_X] at h
  change zCoeff K -
    algebraMap (Polynomial K) (yCoordinateRing K) ((Polynomial.X : Polynomial K) ^ 2) *
        (xCoeff K + zCoeff K) = 0 at h
  rw [map_pow] at h
  exact h

theorem evalYPolynomial_cubic :
    evalYPolynomial K
      (MvPolynomial.X (1 : Fin 3) ^ 2 * MvPolynomial.X (2 : Fin 3) -
        MvPolynomial.X (0 : Fin 3) ^ 2 *
          (MvPolynomial.X (0 : Fin 3) + MvPolynomial.X (2 : Fin 3))) = 0 := by
  simp only [evalYPolynomial, map_sub, map_mul, map_pow, map_add, MvPolynomial.aeval_X]
  simpa [yValues] using yRing_cubic_relation K

theorem yRing_linear_relation :
    (1 - xCoeff K ^ 2) * zCoeff K = xCoeff K ^ 3 := by
  calc
    _ = (zCoeff K - xCoeff K ^ 2 * (xCoeff K + zCoeff K)) + xCoeff K ^ 3 := by ring
    _ = _ := by rw [yRing_cubic_relation, zero_add]

theorem yRing_coefficient_inverse :
    (1 - xCoeff K ^ 2) * (1 + xCoeff K ^ 2 + xCoeff K * zCoeff K) = 1 := by
  calc
    _ = (1 - xCoeff K ^ 2) * (1 + xCoeff K ^ 2) +
      xCoeff K * ((1 - xCoeff K ^ 2) * zCoeff K) := by ring
    _ = _ := by rw [yRing_linear_relation]; ring

theorem yRing_basicOpen_z :
    PrimeSpectrum.basicOpen (zCoeff K) = PrimeSpectrum.basicOpen (xCoeff K) := by
  have hTop : PrimeSpectrum.basicOpen (1 - xCoeff K ^ 2) = ⊤ := by
    have h := PrimeSpectrum.basicOpen_mul (1 - xCoeff K ^ 2)
      (1 + xCoeff K ^ 2 + xCoeff K * zCoeff K)
    rw [yRing_coefficient_inverse, PrimeSpectrum.basicOpen_one] at h
    exact top_unique (h.le.trans inf_le_left)
  calc
    _ = PrimeSpectrum.basicOpen ((1 - xCoeff K ^ 2) * zCoeff K) := by
      simp only [PrimeSpectrum.basicOpen_mul, hTop, top_inf_eq]
    _ = _ := by rw [yRing_linear_relation, PrimeSpectrum.basicOpen_pow _ _ (by decide)]

theorem nodeYInPlane_preimage_z :
    (nodeYInPlane K) ⁻¹ᵁ Proj.basicOpen (grading K) (z K) =
      PrimeSpectrum.basicOpen (xCoeff K) := by
  unfold nodeYInPlane nodeToYChart
  rw [Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen (𝒜 := grading K) (X_mem_one K 1) (by decide)
      (X_mem_one K 2) (by decide), SpecMap_preimage_basicOpen]
  change PrimeSpectrum.basicOpen (evalYChart K (chartCoordinate K 2)) = _
  rw [evalYChart_Z, yRing_basicOpen_z]

end

end ManuscriptAudit.NodalYChartImmersion

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.NodalYChartImmersion.yEquation_printed,
      ``ManuscriptAudit.NodalYChartImmersion.coordinateEquiv,
      ``ManuscriptAudit.NodalYChartImmersion.evalYChart_coordinate,
      ``ManuscriptAudit.NodalYChartImmersion.evalYChart_surjective,
      ``ManuscriptAudit.NodalYChartImmersion.nodeToYChart_closed,
      ``ManuscriptAudit.NodalYChartImmersion.nodeYInPlane_isImmersion,
      ``ManuscriptAudit.NodalYChartImmersion.evalYPolynomial_cubic,
      ``ManuscriptAudit.NodalYChartImmersion.yRing_coefficient_inverse,
      ``ManuscriptAudit.NodalYChartImmersion.nodeYInPlane_preimage_z] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
