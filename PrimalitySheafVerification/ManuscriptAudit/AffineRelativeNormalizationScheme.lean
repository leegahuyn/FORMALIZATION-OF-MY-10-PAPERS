import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Normalization

/-! Relative normalization of a morphism of affine spectra is the spectrum
of the actual integral-closure algebra of the source ring map. -/

namespace ManuscriptAudit.AffineRelativeNormalizationScheme

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

private def transportClosure {R S R' S' : Type u}
    [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [Algebra R S] [Algebra R' S'] (eR : R ≃+* R') (eS : S ≃+* S')
    (h : (algebraMap R' S').comp eR.toRingHom = eS.toRingHom.comp (algebraMap R S)) :
    integralClosure R S ≃+* integralClosure R' S' := by
  have h' : (algebraMap R S).comp eR.symm.toRingHom =
      eS.symm.toRingHom.comp (algebraMap R' S') := by
    apply RingHom.ext
    intro r
    apply eS.injective
    have he := DFunLike.congr_fun h (eR.symm r)
    change algebraMap R' S' (eR (eR.symm r)) =
      eS (algebraMap R S (eR.symm r)) at he
    change eS (algebraMap R S (eR.symm r)) =
      eS (eS.symm (algebraMap R' S' r))
    simpa only [RingEquiv.apply_symm_apply] using he.symm
  exact
    { toFun := fun x => ⟨eS x.val, IsIntegral.map_of_comp_eq _ _ h x.prop⟩
      invFun := fun x => ⟨eS.symm x.val, IsIntegral.map_of_comp_eq _ _ h' x.prop⟩
      left_inv := fun x => Subtype.ext (eS.symm_apply_apply _)
      right_inv := fun x => Subtype.ext (eS.apply_symm_apply _)
      map_mul' := fun x y => Subtype.ext (eS.map_mul _ _)
      map_add' := fun x y => Subtype.ext (eS.map_add _ _) }

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

private abbrev X : Scheme.{u} := Spec (CommRingCat.of S)
private abbrev Y : Scheme.{u} := Spec (CommRingCat.of R)

/-- The morphism of affine spectra coming from the specified algebra. -/
def structureMap : X S ⟶ Y R :=
  Spec.map (CommRingCat.ofHom (algebraMap R S))

private abbrev baseGlobal : CommRingCat.{u} := Γ(Y R, ⊤)
private abbrev sourceGlobal : CommRingCat.{u} := Γ(X S, ⊤)

private instance globalAlgebra : Algebra (baseGlobal R) (sourceGlobal S) :=
  (structureMap R S).appTop.hom.toAlgebra

private def globalClosureIso :
    integralClosure (baseGlobal R) (sourceGlobal S) ≃+* integralClosure R S := by
  let g : CommRingCat.of R ⟶ CommRingCat.of S := CommRingCat.ofHom (algebraMap R S)
  let eR := Scheme.ΓSpecIso (CommRingCat.of R)
  let eS := Scheme.ΓSpecIso (CommRingCat.of S)
  refine transportClosure eR.commRingCatIsoToRingEquiv eS.commRingCatIsoToRingEquiv ?_
  apply RingHom.ext
  intro x
  exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality g) x).symm

private abbrev topChart : (Y R).affineOpens := ⟨⊤, isAffineOpen_top (Y R)⟩

private def topChartIso : Spec (CommRingCat.of (integralClosure (baseGlobal R) (sourceGlobal S))) ≅
    (structureMap R S).normalization := by
  let f := structureMap R S
  let U := topChart R
  let j := f.normalizationOpenCover.f U
  have hr : j.opensRange = ⊤ := by
    rw [← f.fromNormalization_preimage U]
    exact Scheme.Hom.preimage_top _
  have h : Set.range j = Set.range (𝟙 f.normalization) := by
    rw [show Set.range j = Set.univ from congrArg
      (fun W : f.normalization.Opens => (W : Set f.normalization)) hr]
    ext x
    exact ⟨fun _ => ⟨x, rfl⟩, fun _ => Set.mem_univ x⟩
  exact IsOpenImmersion.isoOfRangeEq j (𝟙 _) h

/-- The actual scheme relative normalization over affine spectra. -/
def normalizationSpecIso :
    (structureMap R S).normalization ≅ Spec (CommRingCat.of (integralClosure R S)) :=
  (topChartIso R S).symm ≪≫
    Scheme.Spec.mapIso (globalClosureIso R S).symm.toCommRingCatIso.op

end
end ManuscriptAudit.AffineRelativeNormalizationScheme

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineRelativeNormalizationScheme.normalizationSpecIso
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
