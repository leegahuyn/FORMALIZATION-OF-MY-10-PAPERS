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

private theorem globalClosureIso_algebraMap (x : baseGlobal R) :
    globalClosureIso R S (algebraMap (baseGlobal R) (integralClosure (baseGlobal R) (sourceGlobal S)) x) =
      algebraMap R (integralClosure R S) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom x) := by
  apply Subtype.ext
  change (Scheme.ΓSpecIso (CommRingCat.of S)).hom ((structureMap R S).appTop.hom x) =
    algebraMap R S ((Scheme.ΓSpecIso (CommRingCat.of R)).hom x)
  exact ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R S))) x

/-- The affine normalization isomorphism is over the original target,
with the native integral-closure algebra map. -/
theorem normalizationSpecIso_inv_over :
    (normalizationSpecIso R S).inv ≫ (structureMap R S).fromNormalization =
      structureMap R (integralClosure R S) := by
  let f := structureMap R S
  let U := topChart R
  have ht : (topChartIso R S).hom = f.normalizationOpenCover.f U := by
    rw [← Category.comp_id (topChartIso R S).hom]
    unfold topChartIso
    exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  let c := CommRingCat.ofHom (globalClosureIso R S).toRingHom
  change Spec.map c ≫ (topChartIso R S).hom ≫ f.fromNormalization =
    Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R S)))
  rw [ht, f.ι_fromNormalization]
  have hf : U.2.fromSpec = Spec.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv := by
    change (isAffineOpen_top (Y R)).fromSpec = _
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
  rw [hf, ← Spec.map_comp_assoc, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  change globalClosureIso R S
    (algebraMap (baseGlobal R) (integralClosure (baseGlobal R) (sourceGlobal S))
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv x)) = algebraMap R (integralClosure R S) x
  rw [globalClosureIso_algebraMap]
  exact congrArg (algebraMap R (integralClosure R S))
    (ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of R)).inv_hom_id x)

end
end ManuscriptAudit.AffineRelativeNormalizationScheme

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineRelativeNormalizationScheme.normalizationSpecIso,
      ``ManuscriptAudit.AffineRelativeNormalizationScheme.normalizationSpecIso_inv_over] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName ↦ !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
