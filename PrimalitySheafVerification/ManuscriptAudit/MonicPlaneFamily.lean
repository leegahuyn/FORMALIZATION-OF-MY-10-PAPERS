import Lean.Util.CollectAxioms
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.PolynomialAlgebra

/-! A monic plane equation y²=q(x) gives an actual flat finite-type family;
its scheme pullback along any coefficient extension is the fiber of the
same displayed equation. -/

namespace ManuscriptAudit.MonicPlaneFamily

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Polynomial
open scoped TensorProduct

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- The polynomial in the second plane variable. -/
def equation (q : Polynomial R) : Polynomial (Polynomial R) := X ^ 2 - C q

abbrev coordinateRing (q : Polynomial R) := AdjoinRoot (equation R q)

abbrev family (q : Polynomial R) : Scheme.{u} := Spec (CommRingCat.of (coordinateRing R q))

/-- The literal plane model over the coefficient scheme. -/
def toBase (q : Polynomial R) : family R q ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (coordinateRing R q)))

instance locallyOfFinitePresentation (q : Polynomial R) :
    LocallyOfFinitePresentation (toBase R q) :=
  (LocallyOfFinitePresentation.SpecMap_iff _).mpr
    (RingHom.finitePresentation_algebraMap.mpr
      (inferInstanceAs (Algebra.FinitePresentation R (coordinateRing R q))))

theorem flat_finite_type (q : Polynomial R) :
    Flat (toBase R q) ∧ LocallyOfFiniteType (toBase R q) ∧ QuasiCompact (toBase R q) := by
  let A := coordinateRing R q
  letI : Module.Free R (Polynomial R) := Module.Free.of_basis (Polynomial.basisMonomials R)
  have hm : (equation R q).Monic := Polynomial.monic_X_pow_sub_C q (n := 2) (by decide)
  letI : Module.Free (Polynomial R) A := hm.free_adjoinRoot
  have hF : Module.Flat R A := Module.Flat.trans R (Polynomial R) A
  refine ⟨Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr hF), ?_,
    quasiCompact_of_compactSpace _⟩
  apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
  exact RingHom.finiteType_algebraMap.mpr (inferInstanceAs (Algebra.FiniteType R A))

private def polynomialBaseChange : S ⊗[R] Polynomial R ≃ₐ[S] Polynomial S :=
  (polyEquivTensor' R S).symm

private theorem polynomialBaseChange_tmul_one (f : Polynomial R) :
    polynomialBaseChange R S ((1 : S) ⊗ₜ[R] f) = f.map (algebraMap R S) := by
  change (polyEquivTensor R S).symm ((1 : S) ⊗ₜ[R] f) = f.map (algebraMap R S)
  rw [polyEquivTensor_symm_apply_tmul_eq_smul, one_smul]

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 1600000 in
/-- The actual tensor fiber is the displayed equation after mapping coefficients. -/
def coordinateBaseChange (q : Polynomial R) :
    S ⊗[R] coordinateRing R q ≃ₐ[S] coordinateRing S (q.map (algebraMap R S)) := by
  let T := S ⊗[R] Polynomial R
  letI : CommRing T := inferInstanceAs (CommRing (S ⊗[R] Polynomial R))
  let i : Polynomial R →ₐ[R] T := Algebra.TensorProduct.includeRight
  let e : T ≃ₐ[S] Polynomial S := polynomialBaseChange R S
  let p := equation R q
  let p' : Polynomial T := p.map i.toRingHom
  have hi : e.toRingHom.comp i.toRingHom = Polynomial.mapRingHom (algebraMap R S) := by
    apply RingHom.ext
    intro a
    exact polynomialBaseChange_tmul_one R S a
  have h : p'.map e.toRingHom = equation S (q.map (algebraMap R S)) := by
    change (p.map i.toRingHom).map e.toRingHom = _
    rw [Polynomial.map_map, hi]
    simp only [p, equation, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C] <;> rfl
  have ha : Associated (p'.map e.toRingHom) (equation S (q.map (algebraMap R S))) := by
    rw [h] <;> exact Associated.refl _
  exact (AdjoinRoot.tensorAlgEquiv p p' rfl).trans (AdjoinRoot.mapAlgEquiv e p' _ ha)

private abbrev extendedRing (q : Polynomial R) := S ⊗[R] coordinateRing R q

private def firstProjection (q : Polynomial R) :
    Spec (CommRingCat.of (extendedRing R S q)) ⟶ Spec (CommRingCat.of S) :=
  Spec.map (CommRingCat.ofHom
    ((Algebra.TensorProduct.includeLeft : S →ₐ[R] extendedRing R S q).toRingHom))

private def secondProjection (q : Polynomial R) :
    Spec (CommRingCat.of (extendedRing R S q)) ⟶ family R q :=
  Spec.map (CommRingCat.ofHom
    ((Algebra.TensorProduct.includeRight : coordinateRing R q →ₐ[R] extendedRing R S q).toRingHom))

private theorem tensor_isPullback (q : Polynomial R) :
    IsPullback (firstProjection R S q) (secondProjection R S q)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) (toBase R q) :=
  isPullback_SpecMap_of_isPushout _ _ _ _
    ⟨⟨(CommRingCat.pushoutCocone R S (coordinateRing R q)).condition⟩,
      ⟨CommRingCat.pushoutCoconeIsColimit R S (coordinateRing R q)⟩⟩

/-- Native scheme base change of the actual flat plane model. -/
def schemeBaseChange (q : Polynomial R) :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R S))) (toBase R q) ≅
      family S (q.map (algebraMap R S)) :=
  (tensor_isPullback R S q).isoPullback.symm ≪≫
    Scheme.Spec.mapIso (coordinateBaseChange R S q).symm.toCommRingCatIso.op

/-- The native fiber identification preserves its structural map over the new coefficient ring. -/
theorem schemeBaseChange_over (q : Polynomial R) :
    (schemeBaseChange R S q).hom ≫ toBase S (q.map (algebraMap R S)) =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S))) (toBase R q) := by
  let E := coordinateBaseChange R S q
  let g := Spec.map (CommRingCat.ofHom E.symm.toRingHom)
  have h : g ≫ toBase S (q.map (algebraMap R S)) = firstProjection R S q := by
    unfold toBase firstProjection g
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro t
    change E.symm (algebraMap S (coordinateRing S (q.map (algebraMap R S))) t) =
      algebraMap S (extendedRing R S q) t
    exact E.symm.commutes t
  change ((tensor_isPullback R S q).isoPullback.inv ≫ g) ≫
    toBase S (q.map (algebraMap R S)) = _
  rw [Category.assoc, h]
  exact (tensor_isPullback R S q).isoPullback_inv_fst

end
end ManuscriptAudit.MonicPlaneFamily

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.MonicPlaneFamily.locallyOfFinitePresentation,
      ``ManuscriptAudit.MonicPlaneFamily.flat_finite_type,
      ``ManuscriptAudit.MonicPlaneFamily.coordinateBaseChange,
      ``ManuscriptAudit.MonicPlaneFamily.schemeBaseChange,
      ``ManuscriptAudit.MonicPlaneFamily.schemeBaseChange_over] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
