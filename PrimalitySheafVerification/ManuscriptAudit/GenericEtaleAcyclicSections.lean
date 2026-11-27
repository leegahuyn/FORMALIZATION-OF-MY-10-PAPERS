import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleDomainSite
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleGenericField
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleLocalSurjectivity
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleMorphismInverseImage
import PrimalitySheafVerification.ManuscriptAudit.EtaleFieldChartExactSections
import PrimalitySheafVerification.ManuscriptAudit.GenericEtaleUnitSections

/-!
# Exactness of the generic-point direct image for acyclic sections

The generic fiber of every integral affine étale chart is a field.
Vanishing of the first cohomology of the source sheaf on these field
charts makes the native direct image of the last map epic. Its left
exactness then gives a genuine short exact sheaf sequence.
-/

namespace ManuscriptAudit.GenericEtaleAcyclicSections

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AffineEtaleGenericField GenericEtaleUnitSections SmallEtaleBaseChange
open EtaleObjectRestriction
open scoped TensorProduct

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (A F : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field F]
  [Algebra A F] [IsFractionRing A F]

private abbrev X := Spec (CommRingCat.of A)
private abbrev Y := Spec (CommRingCat.of F)
private abbrev j := Spec.map (CommRingCat.ofHom (algebraMap A F))
private abbrev E := Scheme.AffineEtale.sheafEquiv (X A) AddCommGrpCat.{0}
private abbrev D := directImage (j A F) AddCommGrpCat.{0}
private abbrev M := Sheaf (Y F).smallEtaleTopology AddCommGrpCat.{0}

private instance : (D A F).Additive := ⟨by intros; rfl⟩

variable (C : ShortComplex (M F)) (hC : C.ShortExact)
variable (hVanishing : ∀ (L : Type) [Field L] (g : Spec (CommRingCat.of L) ⟶ Y F)
  [Etale g], Subsingleton (Sheaf.H ((restriction g).obj C.X₁) 1))

include hC hVanishing

set_option maxHeartbeats 3000000 in
private theorem projection_surjective_integral
    (U : (AffineEtaleDomainSite.integralCharts A).FullSubcategory) :
    Function.Surjective (((E A).inverse.map ((D A F).map C.g)).hom.app (op U.obj)) := by
  let B : CommRingCat.{0} := unop U.obj.left
  let a : CommRingCat.of A ⟶ B := Spec.preimage U.obj.hom
  letI : Algebra A B := a.hom.toAlgebra
  letI : IsDomain B := U.property
  have ha : Spec.map a = U.obj.hom := Spec.map_preimage _
  have hEt : Etale (Spec.map a) := ha.symm ▸ U.obj.prop
  have he : (algebraMap A B).Etale := (HasRingHomProperty.Spec_iff (P := @Etale) (φ := a)).mp hEt
  letI : Algebra.Etale A B := RingHom.etale_algebraMap.mp he
  let W := algebraEtaleObject A B
  let V := (Scheme.AffineEtale.Spec (X A)).obj U.obj
  let e : W ≅ V := MorphismProperty.Over.isoMk (Iso.refl (Spec B)) (by
    change 𝟙 (Spec B) ≫ U.obj.hom = Spec.map (CommRingCat.ofHom (algebraMap A B))
    rw [Category.id_comp, show CommRingCat.ofHom (algebraMap A B) = a from CommRingCat.ofHom_hom a, ha])
  let H := etaleBaseChange (j A F)
  let L := F ⊗[A] B
  letI : Field L := (genericFiber_isField A B F).toField
  let S := Scheme.Etale.forget (Y F) ⋙ Over.forget (Y F)
  let e₀ : (H.obj V).left ≅ (H.obj W).left := S.mapIso (H.mapIso e.symm)
  let e₁ : (H.obj W).left ≅ Spec (CommRingCat.of L) := by
    let b := Spec.map (CommRingCat.ofHom (algebraMap A B))
    change pullback b (j A F) ≅ _
    exact pullbackSymmetry b (j A F) ≪≫ pullbackSpecIso A F B
  change Function.Surjective (C.g.hom.app (op (H.obj V)))
  exact sections_surjective_of_HOne_of_field C hC (H.obj V) L (e₀ ≪≫ e₁)
    (fun g _ ↦ hVanishing L g)

set_option maxHeartbeats 2500000 in
private theorem directImage_projection_epi : Epi ((D A F).map C.g) := by
  let S := Scheme.AffineEtale.topology (X A)
  let I := AffineEtaleDomainSite.inclusion A
  letI : I.IsCoverDense S := AffineEtaleDomainSite.integralCharts_coverDense A
  let R := (E A).inverse
  let m := (D A F).map C.g
  let n := R.map m
  letI : Sheaf.IsLocallySurjective n :=
    AffineEtaleLocalSurjectivity.of_coverDense S n.hom I (by
      intro U s
      obtain ⟨x, hx⟩ := projection_surjective_integral A F C hC hVanishing U s
      apply S.superset_covering _ (S.top_mem (I.obj U))
      intro V g _
      refine ⟨(R.obj ((D A F).obj C.X₂)).obj.map g.op x, ?_⟩
      have hx' : n.hom.app (op (I.obj U)) x = s := hx
      exact (NatTrans.naturality_apply n.hom g.op x).trans
        (congrArg ((R.obj ((D A F).obj C.X₃)).obj.map g.op) hx'))
  have h : Epi n := inferInstance
  exact R.epi_of_epi_map h

set_option maxHeartbeats 2500000 in
/-- The generic-point direct image preserves a short exact sequence
whose first term has vanishing H¹ on every étale field chart. -/
theorem directImage_shortExact : (C.map (D A F)).ShortExact := by
  let G := D A F
  obtain ⟨L, ⟨adj⟩, _⟩ := AffineEtaleMorphism.fullDirectImage_hasLeftExactLeftAdjoint
    (CommRingCat.of A) (CommRingCat.of F) (j A F)
  letI : G.IsRightAdjoint := adj.isRightAdjoint
  letI : Mono C.f := hC.mono_f
  have h : (C.map G).Exact := hC.exact.map_of_mono_of_preservesKernel G
    (inferInstanceAs (Mono C.f)) inferInstance
  exact ShortComplex.ShortExact.mk' h (inferInstanceAs (Mono (G.map C.f)))
    (directImage_projection_epi A F C hC hVanishing)

end

end ManuscriptAudit.GenericEtaleAcyclicSections

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.GenericEtaleAcyclicSections.directImage_shortExact
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
