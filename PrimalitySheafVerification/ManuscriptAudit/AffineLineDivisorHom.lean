import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleDomainSite
import PrimalitySheafVerification.ManuscriptAudit.AffineLineChartDivisorMap
import PrimalitySheafVerification.ManuscriptAudit.AffineLineIntegralChartMorphisms

/-!
# The actual generic-unit divisor morphism on the full small étale site

On integral charts the morphism is the native principal divisor. The
integral affine charts are cover-dense, so the morphism extends to all
affine charts and then to the full small étale site.
-/

namespace ManuscriptAudit.AffineLineDivisorSheaf

open AlgebraicGeometry CategoryTheory Opposite
open GenericEtaleUnitSections

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

variable (K F : Type) [Field K] [IsAlgClosed K] [Field F]
  [Algebra (Polynomial K) F] [IsFractionRing (Polynomial K) F]

private abbrev A := Polynomial K
private abbrev E := Scheme.AffineEtale.sheafEquiv (X K) AddCommGrpCat.{0}
private abbrev T := Scheme.AffineEtale.topology (X K)
private abbrev I := AffineEtaleDomainSite.inclusion (A K)
private abbrev source := (E K).inverse.obj (genericUnitImage (A K) F)

private def divisorAtIntegral (U : (AffineEtaleDomainSite.integralCharts (A K)).FullSubcategory) :
    (source K F).obj.obj (op U.obj) ⟶ (affineDivisorSheaf K).obj.obj (op U.obj) := by
  let B := coordinateRing K U.obj
  letI := coordinateAlgebra K U.obj
  letI := coordinateAlgebra_etale K U.obj
  letI : IsDomain B := U.property
  let e := coordinateChartIso K U.obj U.property
  have d : (source K F).obj.obj (op (chartObject K B)) ⟶
      (affineDivisorSheaf K).obj.obj (op (chartObject K B)) :=
    AddCommGrpCat.ofHom (chartDivisorMap K B F)
  exact (source K F).obj.map e.hom.op ≫ d ≫ (affineDivisorSheaf K).obj.map e.inv.op

set_option maxHeartbeats 1800000 in
/-- The divisor on the integral affine charts is a native natural transformation. -/
def integralDivisor :
    (I K).op ⋙ (source K F).obj ⟶ (I K).op ⋙ (affineDivisorSheaf K).obj where
  app U := divisorAtIntegral K F (unop U)
  naturality {U V} h := by
    let U₀ := unop U
    let V₀ := unop V
    let B := coordinateRing K U₀.obj
    let C := coordinateRing K V₀.obj
    letI := coordinateAlgebra K U₀.obj
    letI := coordinateAlgebra K V₀.obj
    letI := coordinateAlgebra_etale K U₀.obj
    letI := coordinateAlgebra_etale K V₀.obj
    letI : IsDomain B := U₀.property
    letI : IsDomain C := V₀.property
    let g := (I K).map h.unop
    let f := coordinateMap K g
    letI : Algebra B C := f.toRingHom.toAlgebra
    letI : IsScalarTower (A K) B C := IsScalarTower.of_algebraMap_eq (fun r ↦ (f.commutes r).symm)
    letI : Algebra.Etale B C := Algebra.Etale.of_restrictScalars (R := A K)
    let e := coordinateChartIso K U₀.obj U₀.property
    let e' := coordinateChartIso K V₀.obj V₀.property
    let b : (source K F).obj.obj (op (chartObject K B)) ⟶
        (affineDivisorSheaf K).obj.obj (op (chartObject K B)) :=
      AddCommGrpCat.ofHom (chartDivisorMap K B F)
    let c : (source K F).obj.obj (op (chartObject K C)) ⟶
        (affineDivisorSheaf K).obj.obj (op (chartObject K C)) :=
      AddCommGrpCat.ofHom (chartDivisorMap K C F)
    have hSquare : e'.hom ≫ g = chartArrow K B C ≫ e.hom :=
      coordinateMap_chart_comm K g U₀.property V₀.property
    have hMap :
        (source K F).obj.map (chartArrow K B C).op ≫ c =
          b ≫ (affineDivisorSheaf K).obj.map (chartArrow K B C).op := by
      apply ConcreteCategory.hom_ext
      intro x
      let G := Scheme.AffineEtale.Spec (X K)
      change chartDivisorMap K C F ((genericUnitImage (A K) F).obj.map
        (G.map (chartArrow K B C)).op x) =
          (affineDivisorSheaf K).obj.map (chartArrow K B C).op (chartDivisorMap K B F x)
      rw [show G.map (chartArrow K B C) =
        algebraEtaleMap (IsScalarTower.toAlgHom (A K) B C) from G.map_preimage _]
      exact chartDivisorMap_restrict K B F C x
    exact transport_restrict e e' g (chartArrow K B C) hSquare b c hMap

/-- The actual divisor morphism on the small affine étale site. -/
def affineDivisorHom : source K F ⟶ affineDivisorSheaf K := by
  letI : (I K).IsCoverDense (T K) :=
    AffineEtaleDomainSite.integralCharts_coverDense (A K)
  exact ⟨Functor.IsCoverDense.sheafHom (integralDivisor K F)⟩

/-- The extended morphism restricts to the specified natural transformation
on the integral affine charts. -/
theorem affineDivisorHom_restrict :
    Functor.whiskerLeft (I K).op (affineDivisorHom K F).hom = integralDivisor K F := by
  letI : (I K).IsCoverDense (T K) :=
    AffineEtaleDomainSite.integralCharts_coverDense (A K)
  exact Functor.IsCoverDense.sheafHom_restrict_eq (integralDivisor K F)

/-- The extended divisor agrees with its actual chosen chart model. -/
theorem affineDivisorHom_app_integral
    (U : (AffineEtaleDomainSite.integralCharts (A K)).FullSubcategory) :
    (affineDivisorHom K F).hom.app (op U.obj) = divisorAtIntegral K F U :=
  NatTrans.congr_app (affineDivisorHom_restrict K F) (op U)

/-- The actual generic-unit divisor morphism on the full small étale site. -/
def divisorHom : genericUnitImage (A K) F ⟶ divisorSheaf K :=
  ((E K).counitIso.app (genericUnitImage (A K) F)).inv ≫
    (E K).functor.map (affineDivisorHom K F)

end

end ManuscriptAudit.AffineLineDivisorSheaf

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineLineDivisorSheaf.integralDivisor,
      ``ManuscriptAudit.AffineLineDivisorSheaf.affineDivisorHom,
      ``ManuscriptAudit.AffineLineDivisorSheaf.affineDivisorHom_restrict,
      ``ManuscriptAudit.AffineLineDivisorSheaf.divisorHom] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
