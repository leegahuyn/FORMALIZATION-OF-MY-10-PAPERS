import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineEtaleTerminalStage
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineProetaleChartTransport

/-! On every actual affine small étale object the genuine inverse
image adjunction unit is bijective on sections. -/

namespace ManuscriptAudit.NativeAffineEtaleUnitBijective

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleAffineTensor (spectrum structureMap)
open NativeAffineEtaleStageSections (etaleObject sectionCocone)
open NativeAffineEtaleTerminalStage (selfStage isTerminal_selfStage unit_app_surjective)
open NativeAffineEtaleRawSections (rawSectionCocone isColimit_rawSectionCocone raw_toNative_fac)
open NativeAffineEtaleKanComparison (toNative)
open EtaleProetaleSiteInclusion (inclusion)
open EtaleProetaleInverseImage (inverseImage directImage adjunction)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A : Type u} [CommRing A]

private abbrev X := spectrum A
private abbrev G := AddCommGrpCat.{u + 1}

variable (I : Sheaf (X (A := A)).smallEtaleTopology G.{u})

private abbrev η := ((adjunction (X (A := A))).unit.app I).hom

set_option maxHeartbeats 3900000 in
/-- The actual affine étale chart evaluates the same as its terminal stage. -/
theorem unit_at_chart {B : Type u} [CommRing B] [Algebra A B] [Algebra.Etale A B]
    [WeaklyEtale (structureMap A B)]
    (hRaw : Function.Bijective ((toNative (X (A := A)) I).app
      (op (ProetaleAffineTensor.object A B)))) :
    Function.Bijective ((η I).app (op (etaleObject (selfStage (A := A) (B := B))))) := by
  refine ⟨?_, unit_app_surjective I hRaw.surjective⟩
  let T := selfStage (A := A) (B := B)
  let c := rawSectionCocone (B := B) I
  letI : IsIso (c.ι.app T) :=
    (isColimit_rawSectionCocone (B := B) I).isIso_ι_app_of_isTerminal T isTerminal_selfStage
  have hc : Function.Injective (c.ι.app T) :=
    (AddCommGrpCat.mono_iff_injective _).mp inferInstance
  intro x y he
  have h := raw_toNative_fac (B := B) I T
  have hl := DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom h) x
  have hr := DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom h) y
  have hEq : (sectionCocone (B := B) I).ι.app T x =
      (sectionCocone (B := B) I).ι.app T y :=
    congrArg (((inverseImage (X (A := A))).obj I).obj.map (NativeAffineEtaleStageSections.chartArrow T).op) he
  exact hc (hRaw.injective (hl.trans (hEq.trans hr.symm)))

set_option maxHeartbeats 5000000 in
/-- The actual adjunction unit evaluates bijectively on any affine
étale object of the actual small étale site. -/
theorem unit_at_affine
    (hRaw : ∀ V : (X (A := A)).ProEt, IsAffine V.left →
      Function.Bijective ((toNative (X (A := A)) I).app (op V)))
    (V : (X (A := A)).Etale) [IsAffine V.left] :
    Function.Bijective ((η I).app (op V)) := by
  let W := (inclusion (X (A := A))).obj V
  letI : IsAffine W.left := inferInstanceAs (IsAffine V.left)
  let B := NativeAffineProetaleChartTransport.coordinateRing W
  have hS : structureMap A B = V.left.isoSpec.inv ≫ V.hom :=
    NativeAffineProetaleChartTransport.structureMap_eq W
  letI : Etale (structureMap A B) := by rw [hS]; infer_instance
  letI : Algebra.Etale A B :=
    (RingHom.etale_algebraMap).mp ((HasRingHomProperty.Spec_iff (P := @Etale)
      (φ := CommRingCat.ofHom (algebraMap A B))).mp inferInstance)
  let U := etaleObject (selfStage (A := A) (B := B))
  let e : U ≅ V := MorphismProperty.Over.isoMk V.left.isoSpec.symm hS.symm
  let H := ((directImage (X (A := A))).obj ((inverseImage (X (A := A))).obj I)).obj
  have hU : Function.Bijective ((η I).app (op U)) :=
    unit_at_chart I (hRaw (ProetaleAffineTensor.object A B) inferInstance)
  have hI : Function.Bijective (I.obj.map e.hom.op) :=
    ⟨(AddCommGrpCat.mono_iff_injective _).mp inferInstance,
      (AddCommGrpCat.epi_iff_surjective _).mp inferInstance⟩
  have hH : Function.Bijective (H.map e.hom.op) :=
    ⟨(AddCommGrpCat.mono_iff_injective _).mp inferInstance,
      (AddCommGrpCat.epi_iff_surjective _).mp inferInstance⟩
  have h (x : I.obj.obj (op V)) :
      (η I).app (op U) (I.obj.map e.hom.op x) =
        H.map e.hom.op ((η I).app (op V) x) :=
    DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom ((η I).naturality e.hom.op)) x
  constructor
  · intro x y he
    exact hI.injective (hU.injective ((h x).trans ((congrArg (H.map e.hom.op) he).trans (h y).symm)))
  · intro x
    obtain ⟨z, hz⟩ := hU.surjective (H.map e.hom.op x)
    obtain ⟨y, hy⟩ := hI.surjective z
    refine ⟨y, hH.injective ?_⟩
    exact (h y).symm.trans ((congrArg ((η I).app (op U)) hy).trans hz)

end
end ManuscriptAudit.NativeAffineEtaleUnitBijective

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NativeAffineEtaleUnitBijective.unit_at_affine
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
