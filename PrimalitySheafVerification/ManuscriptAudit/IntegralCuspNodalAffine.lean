import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspPunctured
import PrimalitySheafVerification.ManuscriptAudit.CuspDelta
import PrimalitySheafVerification.ManuscriptAudit.MonicPlaneFamily
import PrimalitySheafVerification.ManuscriptAudit.NodalProjectiveClosure

/-! Literal flat finite-type families over Spec ℤ with the previously
constructed affine cusp and split node as their actual field fibers. -/

namespace ManuscriptAudit.IntegralCuspNodalAffine

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MonicPlaneFamily
open Polynomial

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev cuspPolynomial (R : Type) [CommRing R] : Polynomial R := X ^ 3
private abbrev nodalPolynomial (R : Type) [CommRing R] : Polynomial R := X ^ 2 * (X + 1)

abbrev integralCusp := family ℤ (cuspPolynomial ℤ)
abbrev integralNode := family ℤ (nodalPolynomial ℤ)

def cuspToInt : integralCusp ⟶ Spec (CommRingCat.of ℤ) :=
  toBase ℤ (cuspPolynomial ℤ)

def nodalToInt : integralNode ⟶ Spec (CommRingCat.of ℤ) :=
  toBase ℤ (nodalPolynomial ℤ)

instance cusp_locallyOfFinitePresentation : LocallyOfFinitePresentation cuspToInt :=
  MonicPlaneFamily.locallyOfFinitePresentation ℤ (cuspPolynomial ℤ)

instance node_locallyOfFinitePresentation : LocallyOfFinitePresentation nodalToInt :=
  MonicPlaneFamily.locallyOfFinitePresentation ℤ (nodalPolynomial ℤ)

theorem cusp_flat_finite_type :
    Flat cuspToInt ∧ LocallyOfFiniteType cuspToInt ∧ QuasiCompact cuspToInt :=
  flat_finite_type ℤ (cuspPolynomial ℤ)

theorem nodal_flat_finite_type :
    Flat nodalToInt ∧ LocallyOfFiniteType nodalToInt ∧ QuasiCompact nodalToInt :=
  flat_finite_type ℤ (nodalPolynomial ℤ)

variable (K : Type) [Field K]

abbrev coefficientPoint : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℤ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℤ K))

private theorem cuspPolynomial_map :
    (cuspPolynomial ℤ).map (algebraMap ℤ K) = cuspPolynomial K := by
  simp only [cuspPolynomial, Polynomial.map_pow, Polynomial.map_X]

private theorem nodalPolynomial_map :
    (nodalPolynomial ℤ).map (algebraMap ℤ K) = nodalPolynomial K := by
  simp only [nodalPolynomial, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add,
    Polynomial.map_X, Polynomial.map_one]

private def familyCongr {p q : Polynomial K} (h : p = q) : family K p ≅ family K q :=
  eqToIso (congrArg (family K) h)

private theorem familyCongr_over {p q : Polynomial K} (h : p = q) :
    (familyCongr K h).hom ≫ toBase K q = toBase K p := by
  subst q
  simp [familyCongr]

private theorem specAlgIso_over {A B : Type} [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] (e : A ≃ₐ[K] B) :
    (Scheme.Spec.mapIso e.symm.toCommRingCatIso.op).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap K B)) =
        Spec.map (CommRingCat.ofHom (algebraMap K A)) := by
  change Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap K B)) = _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact e.symm.commutes

private theorem chained_over {C : Type*} [Category C] {W X Y Z T : C}
    (e₀ : W ≅ X) (e₁ : X ≅ Y) (e₂ : Y ≅ Z)
    {q₀ : W ⟶ T} {q₁ : X ⟶ T} {q₂ : Y ⟶ T} {q₃ : Z ⟶ T}
    (h₂ : e₂.hom ≫ q₃ = q₂) (h₁ : e₁.hom ≫ q₂ = q₁)
    (h₀ : e₀.hom ≫ q₁ = q₀) :
    (e₀ ≪≫ e₁ ≪≫ e₂).hom ≫ q₃ = q₀ := by
  simp only [Iso.trans_hom, Category.assoc, h₂, h₁, h₀]

set_option maxHeartbeats 800000 in
private theorem identifiedFiber_over {B : Type} [CommRing B] [Algebra K B]
    (q : Polynomial ℤ) {p : Polynomial K} (h : q.map (algebraMap ℤ K) = p)
    (e : coordinateRing K p ≃ₐ[K] B) :
    (schemeBaseChange ℤ K q ≪≫ familyCongr K h ≪≫
      Scheme.Spec.mapIso e.symm.toCommRingCatIso.op).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap K B)) =
      pullback.fst (coefficientPoint K) (toBase ℤ q) := by
  let e₀ := schemeBaseChange ℤ K q
  let e₁ := familyCongr K h
  let e₂ := Scheme.Spec.mapIso e.symm.toCommRingCatIso.op
  have h₂ : e₂.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K B)) = toBase K p :=
    specAlgIso_over K e
  have h₁ : e₁.hom ≫ toBase K p = toBase K (q.map (algebraMap ℤ K)) :=
    familyCongr_over K h
  have h₀ : e₀.hom ≫ toBase K (q.map (algebraMap ℤ K)) =
      pullback.fst (coefficientPoint K) (toBase ℤ q) :=
    schemeBaseChange_over ℤ K q
  exact chained_over e₀ e₁ e₂ h₂ h₁ h₀

/-- The native pullback of the integral cusp is the actual affine cusp scheme. -/
def cuspFiberIso :
    pullback (coefficientPoint K) cuspToInt ≅
      Spec (CommRingCat.of (CuspPunctured.CuspSubalgebra K)) :=
  schemeBaseChange ℤ K (cuspPolynomial ℤ) ≪≫ familyCongr K (cuspPolynomial_map K) ≪≫
    Scheme.Spec.mapIso (CuspDelta.paper2_cusp_coordinate_presentation K).symm.toCommRingCatIso.op

theorem cuspFiberIso_over :
    (cuspFiberIso K).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (CuspPunctured.CuspSubalgebra K))) =
        pullback.fst (coefficientPoint K) cuspToInt := by
  unfold cuspFiberIso cuspToInt
  exact identifiedFiber_over K (cuspPolynomial ℤ) (cuspPolynomial_map K)
    (CuspDelta.paper2_cusp_coordinate_presentation K)

/-- The native pullback of the integral node is the same affine nodal
scheme as the singular chart of the proper construction. -/
def nodeFiberIso :
    pullback (coefficientPoint K) nodalToInt ≅ NodalProjectiveClosure.affineNode K :=
  schemeBaseChange ℤ K (nodalPolynomial ℤ) ≪≫ familyCongr K (nodalPolynomial_map K) ≪≫
    Scheme.Spec.mapIso (NodalAffinePresentation.coordinateEquiv K).symm.toCommRingCatIso.op

theorem nodeFiberIso_over :
    (nodeFiberIso K).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (NodalConductor.coordinates K))) =
        pullback.fst (coefficientPoint K) nodalToInt := by
  unfold nodeFiberIso nodalToInt
  exact identifiedFiber_over K (nodalPolynomial ℤ) (nodalPolynomial_map K)
    (NodalAffinePresentation.coordinateEquiv K)

end
end ManuscriptAudit.IntegralCuspNodalAffine

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.IntegralCuspNodalAffine.cusp_flat_finite_type,
      ``ManuscriptAudit.IntegralCuspNodalAffine.nodal_flat_finite_type,
      ``ManuscriptAudit.IntegralCuspNodalAffine.cuspFiberIso,
      ``ManuscriptAudit.IntegralCuspNodalAffine.nodeFiberIso,
      ``ManuscriptAudit.IntegralCuspNodalAffine.cuspFiberIso_over,
      ``ManuscriptAudit.IntegralCuspNodalAffine.nodeFiberIso_over] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
