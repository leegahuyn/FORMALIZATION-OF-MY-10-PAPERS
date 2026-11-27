import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.PolynomialAlgebra

/-! Native base change for an arbitrary equation presented as a polynomial
in the second variable, with polynomial coefficients in the first. -/

namespace ManuscriptAudit.PlaneEquationBaseChange

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
open scoped TensorProduct

noncomputable section

set_option backward.defeqAttrib.useBackward true

universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

abbrev coeffMap : Polynomial R →+* Polynomial S :=
  Polynomial.mapRingHom (algebraMap R S)

abbrev equation (p : Polynomial (Polynomial R)) := p.map (coeffMap R S)

def ringMap (p : Polynomial (Polynomial R)) : AdjoinRoot p →+* AdjoinRoot (equation R S p) :=
  AdjoinRoot.map (coeffMap R S) p (equation R S p) dvd_rfl

theorem ringMap_of (p : Polynomial (Polynomial R)) (a : Polynomial R) :
    ringMap R S p (AdjoinRoot.of p a) =
      AdjoinRoot.of (equation R S p) (coeffMap R S a) :=
  AdjoinRoot.map_of _ _ _ _ _

theorem ringMap_root (p : Polynomial (Polynomial R)) :
    ringMap R S p (AdjoinRoot.root p) = AdjoinRoot.root (equation R S p) :=
  AdjoinRoot.map_root _ _ _ _

private abbrev TP := S ⊗[R] Polynomial R

private abbrev includePolynomial : Polynomial R →ₐ[R] TP R S :=
  Algebra.TensorProduct.includeRight

private abbrev midway (p : Polynomial (Polynomial R)) : Polynomial (TP R S) :=
  p.map (includePolynomial R S).toRingHom

private def polyIso : TP R S ≃ₐ[S] Polynomial S := (polyEquivTensor' R S).symm

private theorem polyIso_right (a : Polynomial R) :
    polyIso R S (includePolynomial R S a) = coeffMap R S a := by
  change (polyEquivTensor R S).symm ((1 : S) ⊗ₜ[R] a) = a.map (algebraMap R S)
  rw [polyEquivTensor_symm_apply_tmul_eq_smul, one_smul]

private theorem map_comp_eq_map {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (p : Polynomial A) (i : A →+* B) (j : B →+* C) (k : A →+* C)
    (h : ∀ a, j (i a) = k a) : (p.map i).map j = p.map k := by
  rw [Polynomial.map_map]
  exact congrArg p.map (RingHom.ext h)

private theorem midway_map (p : Polynomial (Polynomial R)) :
    (midway R S p).map (polyIso R S : TP R S →+* Polynomial S) = equation R S p :=
  map_comp_eq_map p (includePolynomial R S).toRingHom (polyIso R S : TP R S →+* Polynomial S)
    (coeffMap R S) (polyIso_right R S)

private def afterMidway (p : Polynomial (Polynomial R)) :
    AdjoinRoot (midway R S p) ≃ₐ[S] AdjoinRoot (equation R S p) :=
  AdjoinRoot.mapAlgEquiv (polyIso R S) _ _ (by rw [midway_map]; exact Associated.refl _)

/-- The literal scalar-extension tensor of the plane equation is its mapped equation. -/
def coordinateEquiv (p : Polynomial (Polynomial R)) :
    S ⊗[R] AdjoinRoot p ≃ₐ[S] AdjoinRoot (equation R S p) :=
  (AdjoinRoot.tensorAlgEquiv p (midway R S p) rfl).trans (afterMidway R S p)

private theorem afterMidway_of (p : Polynomial (Polynomial R)) (a : TP R S) :
    afterMidway R S p (AdjoinRoot.of (midway R S p) a) =
      AdjoinRoot.of (equation R S p) (polyIso R S a) := by
  unfold afterMidway
  rw [AdjoinRoot.coe_mapAlgEquiv, AdjoinRoot.map_of]

private theorem afterMidway_root (p : Polynomial (Polynomial R)) :
    afterMidway R S p (AdjoinRoot.root (midway R S p)) =
      AdjoinRoot.root (equation R S p) := by
  unfold afterMidway
  rw [AdjoinRoot.coe_mapAlgEquiv, AdjoinRoot.map_root]

/-- The identification also respects the morphism from the original plane algebra. -/
theorem coordinateEquiv_right (p : Polynomial (Polynomial R)) (a : AdjoinRoot p) :
    coordinateEquiv R S p ((1 : S) ⊗ₜ[R] a) = ringMap R S p a := by
  let i : AdjoinRoot p →ₐ[R] S ⊗[R] AdjoinRoot p := Algebra.TensorProduct.includeRight
  have h : (coordinateEquiv R S p).toRingHom.comp i.toRingHom = ringMap R S p := by
    apply AdjoinRoot.ringHom_ext
    · apply RingHom.ext
      intro b
      change coordinateEquiv R S p ((1 : S) ⊗ₜ[R] AdjoinRoot.of p b) =
        ringMap R S p (AdjoinRoot.of p b)
      rw [coordinateEquiv, AlgEquiv.trans_apply, AdjoinRoot.tensorAlgEquiv_of,
        afterMidway_of, ringMap_of]
      exact congrArg (AdjoinRoot.of (equation R S p)) (polyIso_right R S b)
    · change coordinateEquiv R S p ((1 : S) ⊗ₜ[R] AdjoinRoot.root p) =
        ringMap R S p (AdjoinRoot.root p)
      rw [coordinateEquiv, AlgEquiv.trans_apply, AdjoinRoot.tensorAlgEquiv_root,
        afterMidway_root, ringMap_root]
  exact DFunLike.congr_fun h a


abbrev plane (p : Polynomial (Polynomial R)) := Spec (CommRingCat.of (AdjoinRoot p))

def structureMap (p : Polynomial (Polynomial R)) : plane R p ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (AdjoinRoot p)))

abbrev changeBase : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R S))

def planeMap (p : Polynomial (Polynomial R)) : plane S (equation R S p) ⟶ plane R p :=
  Spec.map (CommRingCat.ofHom (ringMap R S p))

private def planePullbackIso (p : Polynomial (Polynomial R)) :
    plane S (equation R S p) ≅ pullback (changeBase R S) (structureMap R p) :=
  Scheme.Spec.mapIso (coordinateEquiv R S p).toCommRingCatIso.op ≪≫
    (pullbackSpecIso R S (AdjoinRoot p)).symm

private theorem planePullbackIso_fst (p : Polynomial (Polynomial R)) :
    (planePullbackIso R S p).hom ≫ pullback.fst (changeBase R S) (structureMap R p) =
      structureMap S (equation R S p) := by
  change (Spec.map (CommRingCat.ofHom (coordinateEquiv R S p).toRingHom) ≫
    (pullbackSpecIso R S (AdjoinRoot p)).inv) ≫
      pullback.fst (changeBase R S) (structureMap R p) = _
  rw [Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact (coordinateEquiv R S p).commutes

private theorem planePullbackIso_snd (p : Polynomial (Polynomial R)) :
    (planePullbackIso R S p).hom ≫ pullback.snd (changeBase R S) (structureMap R p) =
      planeMap R S p := by
  change (Spec.map (CommRingCat.ofHom (coordinateEquiv R S p).toRingHom) ≫
    (pullbackSpecIso R S (AdjoinRoot p)).inv) ≫
      pullback.snd (changeBase R S) (structureMap R p) = _
  rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact coordinateEquiv_right R S p

/-- The actual coefficient diagram of a plane equation is a scheme pullback. -/
theorem square_isPullback (p : Polynomial (Polynomial R)) :
    IsPullback (structureMap S (equation R S p)) (planeMap R S p)
      (changeBase R S) (structureMap R p) := by
  have hf := planePullbackIso_fst R S p
  have hg := planePullbackIso_snd R S p
  refine IsPullback.of_iso_pullback ⟨?_⟩ (planePullbackIso R S p) hf hg
  rw [← hf, ← hg, Category.assoc, Category.assoc, pullback.condition]

end
end ManuscriptAudit.PlaneEquationBaseChange

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.PlaneEquationBaseChange.coordinateEquiv,
      ``ManuscriptAudit.PlaneEquationBaseChange.coordinateEquiv_right,
      ``ManuscriptAudit.PlaneEquationBaseChange.square_isPullback] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
