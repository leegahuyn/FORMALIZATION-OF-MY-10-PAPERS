import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleDomainSite
import PrimalitySheafVerification.ManuscriptAudit.AffineGeometricChartDivisorMap
import PrimalitySheafVerification.ManuscriptAudit.AffineGeometricIntegralChartMorphisms

/-!
# The actual generic-unit divisor morphism on the full small étale site

On integral charts the morphism is the native principal divisor. The
integral affine charts are cover-dense, so the morphism extends to all
affine charts and then to the full small étale site.
-/

namespace ManuscriptAudit.AffineGeometricDivisorHom

open AlgebraicGeometry CategoryTheory Opposite
open GenericEtaleUnitSections AffineGeometricDivisorSheaf AffineGeometricChartDivisorMap
open AffineGeometricDivisorSections AffineGeometricDivisorNaturality
open AffineGeometricIntegralChartCoordinates AffineGeometricIntegralChartMorphisms

noncomputable section

set_option backward.isDefEq.respectTransparency false

private theorem transport_restrict {C : Type*} [Category* C]
    {D : Type*} [Category* D] {F G : Cᵒᵖ ⥤ D}
    {U V U' V' : C} (eu : U' ≅ U) (ev : V' ≅ V)
    (g : V ⟶ U) (g' : V' ⟶ U') (h : ev.hom ≫ g = g' ≫ eu.hom)
    (a : F.obj (op U') ⟶ G.obj (op U')) (b : F.obj (op V') ⟶ G.obj (op V'))
    (hn : F.map g'.op ≫ b = a ≫ G.map g'.op) :
    F.map g.op ≫ (F.map ev.hom.op ≫ b ≫ G.map ev.inv.op) =
      (F.map eu.hom.op ≫ a ≫ G.map eu.inv.op) ≫ G.map g.op := by
  have hf : F.map g.op ≫ F.map ev.hom.op = F.map eu.hom.op ≫ F.map g'.op := by
    rw [← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp, h]
  have hinv : g ≫ eu.inv = ev.inv ≫ g' := by
    apply (cancel_mono eu.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, ← h, Iso.inv_hom_id_assoc]
  have hg : G.map eu.inv.op ≫ G.map g.op = G.map g'.op ≫ G.map ev.inv.op := by
    rw [← G.map_comp, ← G.map_comp, ← op_comp, ← op_comp, hinv]
  calc
    _ = (F.map g.op ≫ F.map ev.hom.op) ≫ b ≫ G.map ev.inv.op := by
      simp only [Category.assoc]
    _ = F.map eu.hom.op ≫ (F.map g'.op ≫ b) ≫ G.map ev.inv.op := by
      rw [hf]
      simp only [Category.assoc]
    _ = F.map eu.hom.op ≫ a ≫ (G.map g'.op ≫ G.map ev.inv.op) := by
      rw [hn]
      simp only [Category.assoc]
    _ = _ := by rw [← hg]; simp only [Category.assoc]

variable (K A F : Type) [Field K] [IsAlgClosed K] [CommRing A] [IsDedekindDomain A]
  [Algebra K A] [Algebra.FiniteType K A] [Field F] [Algebra A F] [IsFractionRing A F]

private abbrev E := Scheme.AffineEtale.sheafEquiv (X A) AddCommGrpCat.{0}
private abbrev T := Scheme.AffineEtale.topology (X A)
private abbrev I := AffineEtaleDomainSite.inclusion A
private abbrev source := (E A).inverse.obj (genericUnitImage A F)

private def divisorAtIntegral (U : (AffineEtaleDomainSite.integralCharts A).FullSubcategory) :
    (source A F).obj.obj (op U.obj) ⟶ (affineDivisorSheaf K A).obj.obj (op U.obj) := by
  let B := coordinateRing A U.obj
  letI := coordinateAlgebra A U.obj
  letI := coordinateAlgebra_etale A U.obj
  letI : IsDomain B := U.property
  let e := coordinateChartIso A U.obj U.property
  have d : (source A F).obj.obj (op (chartObject A B)) ⟶
      (affineDivisorSheaf K A).obj.obj (op (chartObject A B)) :=
    AddCommGrpCat.ofHom (chartDivisorMap K A B F)
  exact (source A F).obj.map e.hom.op ≫ d ≫ (affineDivisorSheaf K A).obj.map e.inv.op

set_option maxHeartbeats 1800000 in
/-- The divisor on the integral affine charts is a native natural transformation. -/
def integralDivisor :
    (I A).op ⋙ (source A F).obj ⟶ (I A).op ⋙ (affineDivisorSheaf K A).obj where
  app U := divisorAtIntegral K A F (unop U)
  naturality {U V} h := by
    let U₀ := unop U
    let V₀ := unop V
    let B := coordinateRing A U₀.obj
    let C := coordinateRing A V₀.obj
    letI : Algebra A B := coordinateAlgebra A U₀.obj
    letI : Algebra A C := coordinateAlgebra A V₀.obj
    letI : Algebra.Etale A B := coordinateAlgebra_etale A U₀.obj
    letI : Algebra.Etale A C := coordinateAlgebra_etale A V₀.obj
    letI : IsDomain B := U₀.property
    letI : IsDomain C := V₀.property
    let g := (I A).map h.unop
    let f : B →ₐ[A] C := coordinateMap A g
    letI : Algebra B C := f.toRingHom.toAlgebra
    letI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq (fun r ↦ (f.commutes r).symm)
    letI : Algebra.Etale B C := Algebra.Etale.of_restrictScalars A B C
    let e := coordinateChartIso A U₀.obj U₀.property
    let e' := coordinateChartIso A V₀.obj V₀.property
    let b : (source A F).obj.obj (op (chartObject A B)) ⟶
        (affineDivisorSheaf K A).obj.obj (op (chartObject A B)) :=
      AddCommGrpCat.ofHom (chartDivisorMap K A B F)
    let c : (source A F).obj.obj (op (chartObject A C)) ⟶
        (affineDivisorSheaf K A).obj.obj (op (chartObject A C)) :=
      AddCommGrpCat.ofHom (chartDivisorMap K A C F)
    have hAlg : IsScalarTower.toAlgHom A B C = f := AlgHom.ext fun _ ↦ rfl
    have hSquare : e'.hom ≫ g = chartArrow A B C ≫ e.hom := by
      change e'.hom ≫ g = (Scheme.AffineEtale.Spec (X A)).preimage
        (X := chartObject A C) (Y := chartObject A B)
        (algebraEtaleMap (IsScalarTower.toAlgHom A B C)) ≫ e.hom
      rw [hAlg]
      exact coordinateMap_chart_comm A g U₀.property V₀.property
    have hMap :
        (source A F).obj.map (chartArrow A B C).op ≫ c =
          b ≫ (affineDivisorSheaf K A).obj.map (chartArrow A B C).op := by
      apply ConcreteCategory.hom_ext
      intro x
      let G := Scheme.AffineEtale.Spec (X A)
      change chartDivisorMap K A C F ((genericUnitImage A F).obj.map
        (G.map (chartArrow A B C)).op x) =
          (affineDivisorSheaf K A).obj.map (chartArrow A B C).op (chartDivisorMap K A B F x)
      rw [show G.map (chartArrow A B C) =
        algebraEtaleMap (IsScalarTower.toAlgHom A B C) from G.map_preimage _]
      exact chartDivisorMap_restrict K A B F C x
    exact transport_restrict e e' g (chartArrow A B C) hSquare b c hMap

/-- The actual divisor morphism on the small affine étale site. -/
def affineDivisorHom : source A F ⟶ affineDivisorSheaf K A := by
  letI : (I A).IsCoverDense (T A) :=
    AffineEtaleDomainSite.integralCharts_coverDense A
  exact ⟨Functor.IsCoverDense.sheafHom (integralDivisor K A F)⟩

/-- The extended morphism restricts to the specified natural transformation
on the integral affine charts. -/
theorem affineDivisorHom_restrict :
    Functor.whiskerLeft (I A).op (affineDivisorHom K A F).hom = integralDivisor K A F := by
  letI : (I A).IsCoverDense (T A) :=
    AffineEtaleDomainSite.integralCharts_coverDense A
  exact Functor.IsCoverDense.sheafHom_restrict_eq (integralDivisor K A F)

/-- The extended divisor agrees with its actual chosen chart model. -/
theorem affineDivisorHom_app_integral
    (U : (AffineEtaleDomainSite.integralCharts A).FullSubcategory) :
    (affineDivisorHom K A F).hom.app (op U.obj) = divisorAtIntegral K A F U :=
  NatTrans.congr_app (affineDivisorHom_restrict K A F) (op U)

/-- The actual generic-unit divisor morphism on the full small étale site. -/
def divisorHom : genericUnitImage A F ⟶ divisorSheaf K A :=
  ((E A).counitIso.app (genericUnitImage A F)).inv ≫
    (E A).functor.map (affineDivisorHom K A F)

end

end ManuscriptAudit.AffineGeometricDivisorHom

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineGeometricDivisorHom.integralDivisor,
      ``ManuscriptAudit.AffineGeometricDivisorHom.affineDivisorHom,
      ``ManuscriptAudit.AffineGeometricDivisorHom.affineDivisorHom_restrict,
      ``ManuscriptAudit.AffineGeometricDivisorHom.divisorHom] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
