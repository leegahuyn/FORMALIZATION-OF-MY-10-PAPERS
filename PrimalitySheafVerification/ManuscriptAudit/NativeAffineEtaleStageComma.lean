import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineEtaleStageCoverage

/-! Actual affine étale stage maps form exactly the pointwise
left Kan extension indexing category at the affine pro-étale chart. -/

namespace ManuscriptAudit.NativeAffineEtaleStageComma

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleAffineTensor (structureMap specMap)
open NativeAffineEtaleStageSections (chartArrow chartArrow_natural etaleObject etaleMap)
open AffineEtaleStageCategory (Stage hom)
open EtaleProetaleSiteInclusion (inclusion)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  [WeaklyEtale (structureMap A B)]

private abbrev X := ProetaleAffineTensor.spectrum A

/-- The actual affine small étale site functor into the actual pro-étale site. -/
abbrev affineInclusion : (X (A := A)).AffineEtale ⥤ (X (A := A)).ProEt :=
  Scheme.AffineEtale.Spec (X (A := A)) ⋙ inclusion (X (A := A))

private instance (T : Stage A B) : Etale (structureMap A T.carrier) :=
  (HasRingHomProperty.Spec_iff (P := @Etale) (φ := CommRingCat.ofHom (algebraMap A T.carrier))).mpr
    ((RingHom.etale_algebraMap).mpr inferInstance)

private abbrev affineObject (T : Stage A B) : (X (A := A)).AffineEtale :=
  Scheme.AffineEtale.mk (structureMap A T.carrier)

private def affineMap {T U : Stage A B} (f : T ⟶ U) :
    affineObject U ⟶ affineObject T :=
  (Scheme.AffineEtale.Spec (X (A := A))).preimage (etaleMap f)

private theorem affineMap_spec {T U : Stage A B} (f : T ⟶ U) :
    (Scheme.AffineEtale.Spec (X (A := A))).map (affineMap f) = etaleMap f :=
  Functor.map_preimage _ _

/-- The actual comma category indexing affine étale sections at this chart. -/
abbrev Index := CostructuredArrow (affineInclusion (A := A)).op
  (op (ProetaleAffineTensor.object A B))

set_option maxHeartbeats 2700000 in
/-- The ring-stage diagram realises those actual geometric chart-to-stage maps. -/
def comparison : Stage A B ⥤ Index (A := A) (B := B) where
  obj T := CostructuredArrow.mk (S := (affineInclusion (A := A)).op)
    (Y := op (affineObject T)) (chartArrow T).op
  map {T U} f := CostructuredArrow.homMk (affineMap f).op (by
    apply Quiver.Hom.unop_inj
    change chartArrow U ≫ (inclusion (X (A := A))).map
      ((Scheme.AffineEtale.Spec (X (A := A))).map (affineMap f)) = chartArrow T
    rw [affineMap_spec]
    exact chartArrow_natural f)
  map_id T := by
    apply CostructuredArrow.hom_ext _ _
    apply Quiver.Hom.unop_inj
    apply (Scheme.AffineEtale.Spec (X (A := A))).map_injective
    change (Scheme.AffineEtale.Spec (X (A := A))).map (affineMap (𝟙 T)) = _
    rw [affineMap_spec, Functor.map_id]
    apply MorphismProperty.Over.Hom.ext
    exact Spec.map_id _
  map_comp f g := by
    apply CostructuredArrow.hom_ext _ _
    apply Quiver.Hom.unop_inj
    apply (Scheme.AffineEtale.Spec (X (A := A))).map_injective
    change (Scheme.AffineEtale.Spec (X (A := A))).map (affineMap (f ≫ g)) =
      (Scheme.AffineEtale.Spec (X (A := A))).map (affineMap g ≫ affineMap f)
    rw [affineMap_spec, Functor.map_comp, affineMap_spec, affineMap_spec]
    apply MorphismProperty.Over.Hom.ext
    exact Spec.map_comp _ _

set_option maxHeartbeats 2700000 in
instance : (comparison (A := A) (B := B)).Faithful where
  map_injective := by
    intro T U f g h
    have hh := congrArg (fun z ↦ z.left.unop) h
    change affineMap f = affineMap g at hh
    have hs := congrArg ((Scheme.AffineEtale.Spec (X (A := A))).map) hh
    rw [affineMap_spec, affineMap_spec] at hs
    have hSch : specMap A (hom f) = specMap A (hom g) :=
      congrArg (fun z : etaleObject U ⟶ etaleObject T ↦ z.left) hs
    have hr := Spec.map_injective hSch
    apply Subtype.ext
    ext x
    exact DFunLike.congr_fun (congrArg (fun z : CommRingCat.of T.carrier ⟶
      CommRingCat.of U.carrier ↦ z.hom) hr) x

set_option maxHeartbeats 3500000 in
instance : (comparison (A := A) (B := B)).Full where
  map_surjective {T U} f := by
    let S := Scheme.AffineEtale.Spec (X (A := A))
    let v : etaleObject U ⟶ etaleObject T := S.map f.left.unop
    let φ : CommRingCat.of T.carrier ⟶ CommRingCat.of U.carrier := Spec.preimage v.left
    have hφ : Spec.map φ = v.left := Spec.map_preimage v.left
    have hA : CommRingCat.ofHom (algebraMap A T.carrier) ≫ φ =
        CommRingCat.ofHom (algebraMap A U.carrier) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hφ]
      exact MorphismProperty.Over.w v
    let a : T.carrier →ₐ[A] U.carrier :=
      { toRingHom := φ.hom
        commutes' := fun x ↦ DFunLike.congr_fun (congrArg
          (fun z : CommRingCat.of A ⟶ CommRingCat.of U.carrier ↦ z.hom) hA) x }
    have hEq : φ ≫ CommRingCat.ofHom U.toChart.toRingHom =
        CommRingCat.ofHom T.toChart.toRingHom := by
      apply Spec.map_injective
      rw [Spec.map_comp, hφ]
      have h := congrArg
        (fun m : (affineInclusion (A := A)).op.obj (op (affineObject T)) ⟶
          op (ProetaleAffineTensor.object A B) ↦ m.unop.left) (CostructuredArrow.w f)
      change specMap A U.toChart ≫ v.left = specMap A T.toChart at h
      exact h
    let m : T ⟶ U := ⟨a, by
      ext x
      exact DFunLike.congr_fun (congrArg (fun z : CommRingCat.of T.carrier ⟶
        CommRingCat.of B ↦ z.hom) hEq) x⟩
    refine ⟨m, ?_⟩
    apply CostructuredArrow.hom_ext _ _
    apply Quiver.Hom.unop_inj
    apply S.map_injective
    change S.map (affineMap m) = v
    rw [show S.map (affineMap m) = etaleMap m from affineMap_spec m]
    apply MorphismProperty.Over.Hom.ext
    exact hφ

set_option maxHeartbeats 3300000 in
instance : (comparison (A := A) (B := B)).EssSurj where
  mem_essImage W := by
    let S := Scheme.AffineEtale.Spec (X (A := A))
    let V : (X (A := A)).Etale := S.obj W.left.unop
    letI : IsAffine V.left := inferInstanceAs (IsAffine (Spec _))
    let f : ProetaleAffineTensor.object A B ⟶ (inclusion (X (A := A))).obj V := W.hom.unop
    obtain ⟨T, e, he⟩ := NativeAffineEtaleStageCoverage.exists_stage V f
    let j : affineObject T ≅ W.left.unop := S.preimageIso e
    have hj : S.map j.hom = e.hom := by simp [j]
    let e' : W.left ≅ op (affineObject T) := j.op
    have h : (affineInclusion (A := A)).op.map e'.hom ≫
        ((comparison (A := A) (B := B)).obj T).hom = W.hom := by
      apply Quiver.Hom.unop_inj
      change chartArrow T ≫ (inclusion (X (A := A))).map (S.map j.hom) = f
      rwa [hj]
    exact ⟨T, ⟨(CostructuredArrow.isoMk e' h).symm⟩⟩

/-- The literal affine étale stage diagram is the actual geometric
pointwise Kan extension comma category. -/
def equivalence : Stage A B ≌ Index (A := A) (B := B) :=
  (comparison (A := A) (B := B)).asEquivalence

/-- The geometric comma equivalence preserves the stage targets on the
actual small étale site. -/
def etaleDiagramIso :
    (comparison (A := A) (B := B)) ⋙
      CostructuredArrow.proj (affineInclusion (A := A)).op
        (op (ProetaleAffineTensor.object A B)) ⋙ (Scheme.AffineEtale.Spec (X (A := A))).op ≅
      NativeAffineEtaleStageSections.etaleDiagram (A := A) (B := B) :=
  NatIso.ofComponents (fun T ↦ Iso.refl (op (etaleObject T))) (by
    intro T U f
    change ((Scheme.AffineEtale.Spec (X (A := A))).map (affineMap f)).op ≫ 𝟙 _ =
      𝟙 _ ≫ (etaleMap f).op
    rw [Category.comp_id, Category.id_comp, affineMap_spec])

end
end ManuscriptAudit.NativeAffineEtaleStageComma

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NativeAffineEtaleStageComma.equivalence
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
