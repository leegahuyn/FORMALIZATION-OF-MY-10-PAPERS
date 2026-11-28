import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import PrimalitySheafVerification.ManuscriptAudit.CuspProperCompactification

/-! The proper schematic closure of the literal affine Weierstrass equation. -/

namespace ManuscriptAudit.WeierstrassProjectiveClosure

open AlgebraicGeometry CategoryTheory Polynomial WeierstrassCurve.Affine
open CuspProperCompactification
open scoped Polynomial.Bivariate

universe u

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} [Field K] (W : WeierstrassCurve.Affine K)

def chartValues (i : Fin 3) : W.CoordinateRing :=
  if i = 0 then CoordinateRing.mk W (C X) else if i = 1 then CoordinateRing.mk W Y else 1

theorem chartValues_Z : chartValues W 2 = 1 := by simp [chartValues]

def chartEvaluation : standardZChartRing K →+* W.CoordinateRing :=
  standardZChartEvaluation K (chartValues W) (chartValues_Z W)

private theorem variable_x_in_range : ∃ f, chartEvaluation W f = CoordinateRing.mk W (C X) :=
  ⟨_, by
    simpa [chartEvaluation, chartValues] using
      standardZChartEvaluation_X K (chartValues W) (chartValues_Z W) 0⟩

private theorem variable_y_in_range : ∃ f, chartEvaluation W f = CoordinateRing.mk W Y :=
  ⟨_, by
    simpa [chartEvaluation, chartValues] using
      standardZChartEvaluation_X K (chartValues W) (chartValues_Z W) 1⟩

set_option maxHeartbeats 2000000 in
/-- All polynomials on the literal affine Weierstrass chart are obtained
by restriction from the standard projective-plane Z chart. -/
theorem chartEvaluation_surjective : Function.Surjective (chartEvaluation W) := by
  let g : K[X] →+* W.CoordinateRing := (CoordinateRing.mk W).comp C
  have hX : ∃ f, chartEvaluation W f = g X := variable_x_in_range W
  have hC (a : K) : ∃ f, chartEvaluation W f = g (C a) :=
    ⟨_, standardZChartEvaluation_C K (chartValues W) (chartValues_Z W) a⟩
  have hs (p : K[X]) : ∃ f, chartEvaluation W f = g p := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      obtain ⟨u, hu⟩ := hp
      obtain ⟨v, hv⟩ := hq
      exact ⟨u + v, by rw [map_add, map_add, hu, hv]⟩
    | monomial n a =>
      obtain ⟨u, hu⟩ := hC a
      obtain ⟨v, hv⟩ := hX
      exact ⟨u * v ^ n, by rw [map_mul, map_pow, hu, hv, ← C_mul_X_pow_eq_monomial, map_mul, map_pow]⟩
  intro r
  obtain ⟨p, q, hr⟩ := CoordinateRing.exists_smul_basis_eq r
  obtain ⟨p', hp⟩ := hs p
  obtain ⟨q', hq⟩ := hs q
  obtain ⟨y', hy⟩ := variable_y_in_range W
  refine ⟨p' + q' * y', ?_⟩
  rw [map_add, map_mul, hp, hq, hy, ← hr, CoordinateRing.smul, CoordinateRing.smul, mul_one] <;> rfl

abbrev affineScheme := Spec (CommRingCat.of W.CoordinateRing)

/-- The actual Weierstrass affine chart inside the standard projective plane. -/
def inPlane : affineScheme W ⟶ projectivePlane K :=
  Spec.map (CommRingCat.ofHom (chartEvaluation W)) ≫ affineZChartι K

private instance inPlane_isImmersion : IsImmersion (inPlane W) := by
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (chartEvaluation W))) :=
    IsClosedImmersion.spec_of_surjective _ (chartEvaluation_surjective W)
  unfold inPlane
  infer_instance

private instance inPlane_quasiCompact : QuasiCompact (inPlane W) :=
  quasiCompact_of_compactSpace _

/-- The genuine projective schematic closure of the Weierstrass chart. -/
abbrev projectiveScheme : Scheme.{u} := (inPlane W).image

def affineOpen : affineScheme W ⟶ projectiveScheme W := (inPlane W).toImage

def toBase : projectiveScheme W ⟶ Spec (CommRingCat.of K) :=
  (inPlane W).imageι ≫ projectivePlaneToBase K

theorem toBase_isProper : IsProper (toBase W) := by
  letI : IsProper (projectivePlaneToBase K) := projectivePlaneToBase_isProper K
  unfold toBase
  infer_instance

instance affineOpen_isOpenImmersion : IsOpenImmersion (affineOpen W) := by
  unfold affineOpen
  infer_instance

theorem affineOpen_isDominant : IsDominant (affineOpen W) := by
  unfold affineOpen
  infer_instance

theorem affineOpen_toBase :
    affineOpen W ≫ toBase W =
      Spec.map (CommRingCat.ofHom (algebraMap K W.CoordinateRing)) := by
  unfold affineOpen toBase
  rw [← Category.assoc, Scheme.Hom.toImage_imageι]
  unfold inPlane chartEvaluation
  rw [Category.assoc]
  exact standardZChartPoint_toBase K (chartValues W) (chartValues_Z W)

end

end ManuscriptAudit.WeierstrassProjectiveClosure

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassProjectiveClosure.chartEvaluation_surjective,
      ``ManuscriptAudit.WeierstrassProjectiveClosure.toBase_isProper,
      ``ManuscriptAudit.WeierstrassProjectiveClosure.affineOpen_isOpenImmersion,
      ``ManuscriptAudit.WeierstrassProjectiveClosure.affineOpen_isDominant,
      ``ManuscriptAudit.WeierstrassProjectiveClosure.affineOpen_toBase] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
