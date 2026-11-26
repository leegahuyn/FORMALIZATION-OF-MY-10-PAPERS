import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.GenericEtaleUnitComparison

/-!
# Restriction of generic-point units between actual affine charts

The tensor-product descriptions of the generic-point direct image
commute with the genuine restrictions on the small étale site.
-/

namespace ManuscriptAudit.GenericEtaleUnitSections

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open KummerUnitsSheaf SmallEtaleBaseChange
open scoped TensorProduct

noncomputable section

set_option backward.isDefEq.respectTransparency false

private abbrev specAlgebraMap (A B : Type) [CommRing A] [CommRing B] [Algebra A B] :
    Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A B))

variable {A B C F : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing F]
  [Algebra A B] [Algebra A C] [Algebra A F] [Algebra.Etale A B] [Algebra.Etale A C]

/-- The actual arrow of affine étale objects induced by an algebra homomorphism. -/
def algebraEtaleMap (f : B →ₐ[A] C) : algebraEtaleObject A C ⟶ algebraEtaleObject A B :=
  MorphismProperty.Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom f.toRingHom) ≫ specAlgebraMap A B = specAlgebraMap A C
    simp only [specAlgebraMap, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    exact f.commutes)

private abbrev chart (A B F : Type) [CommRing A] [CommRing B] [CommRing F]
    [Algebra A B] [Algebra A F] :
    pullback (specAlgebraMap A B) (specAlgebraMap A F) ≅
      Spec (CommRingCat.of (F ⊗[A] B)) :=
  pullbackSymmetry _ _ ≪≫ pullbackSpecIso A F B

private abbrev specRight (A B F : Type) [CommRing A] [CommRing B] [CommRing F]
    [Algebra A B] [Algebra A F] :
    Spec (CommRingCat.of (F ⊗[A] B)) ⟶ Spec (CommRingCat.of B) :=
  Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : B →ₐ[A] F ⊗[A] B).toRingHom)

@[reassoc (attr := simp)]
private theorem chart_hom_fst (A B F : Type) [CommRing A] [CommRing B] [CommRing F]
    [Algebra A B] [Algebra A F] :
    (chart A B F).hom ≫ specRight A B F = pullback.fst _ _ := by
  simp [chart, specRight, specAlgebraMap, Category.assoc]

@[reassoc (attr := simp)]
private theorem chart_hom_snd (A B F : Type) [CommRing A] [CommRing B] [CommRing F]
    [Algebra A B] [Algebra A F] :
    (chart A B F).hom ≫ specAlgebraMap F (F ⊗[A] B) = pullback.snd _ _ := by
  simp [chart, specAlgebraMap, Category.assoc]

private theorem chart_inv_fst (A B F : Type) [CommRing A] [CommRing B] [CommRing F]
    [Algebra A B] [Algebra A F] :
    (chart A B F).inv ≫ pullback.fst _ _ = specRight A B F := by
  rw [← chart_hom_fst A B F, Iso.inv_hom_id_assoc]

private theorem chart_inv_snd (A B F : Type) [CommRing A] [CommRing B] [CommRing F]
    [Algebra A B] [Algebra A F] :
    (chart A B F).inv ≫ pullback.snd _ _ = specAlgebraMap F (F ⊗[A] B) := by
  rw [← chart_hom_snd A B F, Iso.inv_hom_id_assoc]

set_option maxHeartbeats 800000 in
private theorem chart_inv_naturality (f : B →ₐ[A] C) :
    (chart A C F).inv ≫ ((etaleBaseChange (specAlgebraMap A F)).map (algebraEtaleMap f)).left =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id A F) f).toRingHom) ≫ (chart A B F).inv := by
  let j := specAlgebraMap A F
  let g := algebraEtaleMap f
  let m := (etaleBaseChange j).map g
  let n := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.map (AlgHom.id A F) f).toRingHom)
  have hn₁ : n ≫ specRight A B F = specRight A C F ≫ g.left := by
    change n ≫ specRight A B F = specRight A C F ≫ Spec.map (CommRingCat.ofHom f.toRingHom)
    simp only [n, specRight, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    change (Algebra.TensorProduct.map (AlgHom.id A F) f) ((1 : F) ⊗ₜ[A] x) =
      (1 : F) ⊗ₜ[A] f x
    simp
  have hn₂ : n ≫ specAlgebraMap F (F ⊗[A] B) = specAlgebraMap F (F ⊗[A] C) := by
    simp only [n, specAlgebraMap, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    change (Algebra.TensorProduct.map (AlgHom.id A F) f) (x ⊗ₜ[A] (1 : B)) =
      x ⊗ₜ[A] (1 : C)
    simp
  have h₁ : m.left ≫ pullback.fst (specAlgebraMap A B) j =
      pullback.fst (specAlgebraMap A C) j ≫ g.left := by
    simp only [m, etaleBaseChange, MorphismProperty.Over.pullback_map_left, pullback.lift_fst]
  have h₂ : m.left ≫ pullback.snd (specAlgebraMap A B) j =
      pullback.snd (specAlgebraMap A C) j := by
    simp only [m, etaleBaseChange, MorphismProperty.Over.pullback_map_left, pullback.lift_snd]
  change (chart A C F).inv ≫ m.left = n ≫ (chart A B F).inv
  apply pullback.hom_ext
  · simp only [Category.assoc, h₁, chart_inv_fst, hn₁, ← Category.assoc]
  · simp only [Category.assoc, h₂, chart_inv_snd, hn₂]

section FractionField

variable (A B C F : Type) [CommRing A] [IsDomain A] [CommRing B] [CommRing C] [Field F]
  [Algebra A B] [Algebra A C] [Algebra A F] [IsFractionRing A F]
  [Algebra.Etale A B] [Algebra.Etale A C]

/-- Restriction of actual direct-image sections equals the map induced by the tensor
product of the algebra homomorphism with the fraction field. -/
theorem genericUnitSectionsIso_naturality (f : B →ₐ[A] C) :
    (genericUnitImage A F).obj.map (algebraEtaleMap f).op ≫ (genericUnitSectionsIso A C F).hom =
      (genericUnitSectionsIso A B F).hom ≫ ringUnits.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id A F) f).toRingHom) := by
  let m := ((etaleBaseChange (specAlgebraMap A F)).map (algebraEtaleMap f)).left
  let i : CommRingCat.of (F ⊗[A] B) ⟶ CommRingCat.of (F ⊗[A] C) :=
    CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A F) f).toRingHom
  let e := (chart A B F).inv
  let e' := (chart A C F).inv
  have h : e' ≫ m = Spec.map i ≫ e := chart_inv_naturality f
  have hTop : m.appTop ≫ e'.appTop = e.appTop ≫ (Spec.map i).appTop := by
    simpa only [Scheme.Hom.comp_appTop] using congrArg Scheme.Hom.appTop h
  change ringUnits.map m.appTop ≫ ringUnits.map (e'.appTop ≫ (Scheme.ΓSpecIso _).hom) =
    ringUnits.map (e.appTop ≫ (Scheme.ΓSpecIso _).hom) ≫ ringUnits.map i
  rw [← ringUnits.map_comp, ← ringUnits.map_comp, ← Category.assoc, hTop, Category.assoc,
    Scheme.ΓSpecIso_naturality, ← Category.assoc]

end FractionField

end

end ManuscriptAudit.GenericEtaleUnitSections

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.GenericEtaleUnitSections.genericUnitSectionsIso_naturality
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
