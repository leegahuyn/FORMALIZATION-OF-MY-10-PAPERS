import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Ring.LinearAlgebra
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.PolynomialAlgebra

/-!
# The actual smooth affine-line family and its fiber over five

The family is the spectrum of the polynomial ring over the integers.
Tensor base change identifies its scheme fiber over five with the
same polynomial ring over F₅ used by the arithmetic H¹ computation.
-/

namespace ManuscriptAudit.ArithmeticLineModel

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

noncomputable section

def lineMap (R : Type) [CommRing R] :
    Spec (CommRingCat.of (Polynomial R)) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (Polynomial R)))

theorem line_smooth (R : Type) [CommRing R] : Smooth (lineMap R) :=
  (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
    (RingHom.smooth_algebraMap.mpr ⟨inferInstance, inferInstance⟩)

attribute [local instance] line_smooth

theorem integral_model_flat_finite_type :
    Flat (lineMap ℤ) ∧ LocallyOfFiniteType (lineMap ℤ) ∧ QuasiCompact (lineMap ℤ) := by
  have hq : QuasiCompact (Spec.map
      (CommRingCat.ofHom (algebraMap ℤ (Polynomial ℤ)))) := inferInstance
  exact ⟨inferInstance, inferInstance, hq⟩

abbrev Five := ZMod 5
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

def residueMap : Spec (CommRingCat.of Five) ⟶ Spec (CommRingCat.of ℤ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℤ Five))

theorem residueMap_kernel :
    RingHom.ker (algebraMap ℤ Five) = Ideal.span ({5} : Set ℤ) := by
  ext n
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  exact ZMod.intCast_zmod_eq_zero_iff_dvd n 5

private abbrev tensorRing : Type := Five ⊗[ℤ] Polynomial ℤ
private abbrev tensorScheme := Spec (CommRingCat.of tensorRing)

private def toResidue : tensorScheme ⟶ Spec (CommRingCat.of Five) :=
  Spec.map (CommRingCat.ofHom
    ((Algebra.TensorProduct.includeLeft : Five →ₐ[ℤ] tensorRing).toRingHom))

private def toIntegralLine : tensorScheme ⟶ Spec (CommRingCat.of (Polynomial ℤ)) :=
  Spec.map (CommRingCat.ofHom
    ((Algebra.TensorProduct.includeRight : Polynomial ℤ →ₐ[ℤ] tensorRing).toRingHom))

private theorem tensor_isPullback : IsPullback toResidue toIntegralLine residueMap (lineMap ℤ) :=
  isPullback_SpecMap_of_isPushout _ _ _ _
    ⟨⟨(CommRingCat.pushoutCocone ℤ Five (Polynomial ℤ)).condition⟩,
      ⟨CommRingCat.pushoutCoconeIsColimit ℤ Five (Polynomial ℤ)⟩⟩

abbrev fiberFive := pullback (lineMap ℤ) residueMap

def fiberFiveIso : fiberFive ≅ Spec (CommRingCat.of (Polynomial Five)) :=
  tensor_isPullback.flip.isoPullback.symm ≪≫
    Scheme.Spec.mapIso (polyEquivTensor ℤ Five).toRingEquiv.toCommRingCatIso.op

theorem fiber_coordinate_dimension (K : Type) [Field K] : ringKrullDim (Polynomial K) = 1 :=
  IsPrincipalIdealRing.ringKrullDim_eq_one (Polynomial K) Polynomial.polynomial_not_isField

theorem fiber_coordinate_normal : IsIntegrallyClosed (Polynomial Five) := by
  classical
  letI : GCDMonoid (Polynomial Five) := EuclideanDomain.gcdMonoid _
  infer_instance

theorem fiber_one_component : IrreducibleSpace (Spec (CommRingCat.of (Polynomial Five))) :=
  inferInstanceAs (IrreducibleSpace (PrimeSpectrum (Polynomial Five)))

def singularPoints : Set (Spec (CommRingCat.of (Polynomial Five))) :=
  {x | x ∉ (lineMap Five).smoothLocus}

theorem singularPoints_eq_empty : singularPoints = ∅ := by
  ext x
  change (x ∉ (lineMap Five).smoothLocus) ↔ x ∈ (∅ : Set _)
  rw [Scheme.Hom.smoothLocus_eq_top]
  simp

end

end ManuscriptAudit.ArithmeticLineModel

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in
    [``ManuscriptAudit.ArithmeticLineModel.integral_model_flat_finite_type,
      ``ManuscriptAudit.ArithmeticLineModel.residueMap_kernel,
      ``ManuscriptAudit.ArithmeticLineModel.fiberFiveIso,
      ``ManuscriptAudit.ArithmeticLineModel.fiber_coordinate_dimension,
      ``ManuscriptAudit.ArithmeticLineModel.fiber_coordinate_normal,
      ``ManuscriptAudit.ArithmeticLineModel.fiber_one_component,
      ``ManuscriptAudit.ArithmeticLineModel.singularPoints_eq_empty] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter (fun axiomName => !allowed.contains axiomName)
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
