import Lean.Util.CollectAxioms
import Mathlib.Tactic.FinCases
import PrimalitySheafVerification.ManuscriptAudit.ProjectivePlaneSemilinearAway
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassSemilinearCoordinate
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassProjectiveClosure

/-! Semilinear coefficient transport commutes with the literal affine
Weierstrass embedding in the genuine projective plane. -/

namespace ManuscriptAudit.WeierstrassSemilinearAffineChart

open AlgebraicGeometry CategoryTheory Opposite Polynomial WeierstrassCurve.Affine
open HomogeneousLocalization CuspYChartAlgebra CuspProperCompactification
open WeierstrassSemilinearCoordinate ProjectivePlaneSemilinear ProjectivePlaneSemilinearAway
open WeierstrassProjectiveClosure
open scoped Polynomial.Bivariate

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
variable {K L : Type u} [Field K] [Field L]
variable (W : WeierstrassCurve.Affine K) (e : K ≃+* L)

private abbrev W' := W.map e.toRingHom
private abbrev Φ := coordinateEquiv W e

theorem coordinate_constant (a : K) :
    Φ W e (algebraMap K W.CoordinateRing a) =
      algebraMap L (W' W e).CoordinateRing (e a) := by
  change CoordinateRing.map W e.toRingHom (CoordinateRing.mk W (C (C a))) =
    CoordinateRing.mk (W' W e) (C (C (e a)))
  rw [CoordinateRing.map_mk]
  simp only [Polynomial.map_C, Polynomial.coe_mapRingHom] <;> rfl

private theorem coordinate_variables (i : Fin 3) :
    Φ W e (chartValues W i) = chartValues (W' W e) i := by
  fin_cases i
  · change CoordinateRing.map W e.toRingHom (CoordinateRing.mk W (C X)) =
      CoordinateRing.mk (W' W e) (C X)
    rw [CoordinateRing.map_mk, Polynomial.map_C, Polynomial.coe_mapRingHom, Polynomial.map_X]
  · change CoordinateRing.map W e.toRingHom (CoordinateRing.mk W Y) =
      CoordinateRing.mk (W' W e) Y
    rw [CoordinateRing.map_mk, Polynomial.map_X]
  · change Φ W e 1 = 1
    exact map_one _

private abbrev ev {F : Type u} [Field F] (V : WeierstrassCurve.Affine F) :
    MvPolynomial (Fin 3) F →+* V.CoordinateRing :=
  (MvPolynomial.aeval (R := F) (chartValues V)).toRingHom

private theorem evaluation_natural :
    (Φ W e).toRingHom.comp (ev W) =
      (ev (W' W e)).comp (coefficientMap e.toRingHom).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro a
    change Φ W e (MvPolynomial.aeval (chartValues W) (MvPolynomial.C a)) =
      MvPolynomial.aeval (chartValues (W' W e)) (coefficientMap e.toRingHom (MvPolynomial.C a))
    rw [coefficientMap_const, MvPolynomial.aeval_C, MvPolynomial.aeval_C, coordinate_constant]
  · intro i
    change Φ W e (MvPolynomial.aeval (chartValues W) (MvPolynomial.X i)) =
      MvPolynomial.aeval (chartValues (W' W e)) (coefficientMap e.toRingHom (MvPolynomial.X i))
    rw [coefficientMap_var, MvPolynomial.aeval_X, MvPolynomial.aeval_X, coordinate_variables]

private abbrev zMap : standardZChartRing K →+* standardZChartRing L :=
  mapAway e (z K) (z L) (coefficientMap_var e.toRingHom 2)

theorem chartEvaluation_natural :
    (Φ W e).toRingHom.comp (chartEvaluation W) =
      (chartEvaluation (W' W e)).comp (zMap e) := by
  apply RingHom.ext
  intro v
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective (grading K) (X_mem_one K 2) v
  change Φ W e (standardZChartEvaluation K (chartValues W) (chartValues_Z W)
      (Away.mk (grading K) (X_mem_one K 2) n a ha)) =
    standardZChartEvaluation L (chartValues (W' W e)) (chartValues_Z (W' W e))
      (zMap e (Away.mk (grading K) (X_mem_one K 2) n a ha))
  rw [standardZChartEvaluation_mk,
    mapAway_mk e (z K) (z L) (coefficientMap_var e.toRingHom 2)
      (X_mem_one K 2) (X_mem_one L 2),
    standardZChartEvaluation_mk]
  exact DFunLike.congr_fun (evaluation_natural W e) a

/-- The native affine scheme isomorphism induced by the literal
semilinear isomorphism of the coordinate ring. -/
def affineSchemeIso : affineScheme (W' W e) ≅ affineScheme W :=
  Scheme.Spec.mapIso (coordinateEquiv W e).toCommRingCatIso.op

/-- The actual semilinear map gives the commuting affine embedding square. -/
theorem inPlane_semilinear :
    (affineSchemeIso W e).hom ≫ inPlane W =
      inPlane (W' W e) ≫ (planeIso e).hom := by
  let d₀ := CommRingCat.ofHom (chartEvaluation W)
  let d₁ := CommRingCat.ofHom (chartEvaluation (W' W e))
  let c := CommRingCat.ofHom (Φ W e).toRingHom
  let a := CommRingCat.ofHom (zMap e)
  have hz : affineZChartι L ≫ (planeIso e).hom = Spec.map a ≫ affineZChartι K :=
    awayι_planeIso e (z K) (z L) (coefficientMap_var e.toRingHom 2)
      (X_mem_one K 2) (X_mem_one L 2) (by decide)
  have h : d₀ ≫ c = a ≫ d₁ := CommRingCat.hom_ext (chartEvaluation_natural W e)
  change Spec.map c ≫ (Spec.map d₀ ≫ affineZChartι K) =
    (Spec.map d₁ ≫ affineZChartι L) ≫ (planeIso e).hom
  calc
    _ = Spec.map (d₀ ≫ c) ≫ affineZChartι K := by rw [Spec.map_comp, Category.assoc]
    _ = Spec.map (a ≫ d₁) ≫ affineZChartι K := congrArg (fun z => Spec.map z ≫ affineZChartι K) h
    _ = Spec.map d₁ ≫ (Spec.map a ≫ affineZChartι K) := by rw [Spec.map_comp, Category.assoc]
    _ = _ := by rw [← hz, Category.assoc]

end

end ManuscriptAudit.WeierstrassSemilinearAffineChart

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.WeierstrassSemilinearAffineChart.inPlane_semilinear
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
