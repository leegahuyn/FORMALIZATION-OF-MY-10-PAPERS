import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineEtaleRawStageElements
import PrimalitySheafVerification.ManuscriptAudit.AffineStageFinitePresentationContinuity
import PrimalitySheafVerification.ManuscriptAudit.AffineStageTensorLegs

/-! The raw affine section diagram is compatible with arbitrary
filtered diagrams of genuinely weakly étale affine chart rings. -/

namespace ManuscriptAudit.NativeAffineUnderRingRawSections

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleAffineTensor (spectrum structureMap)
open AffineEtaleStageCategory (Stage)
open AffineStageTensorLegs (algebraHom)
open NativeAffineEtaleStageSections (sectionDiagram)
open NativeAffineEtaleRawSections (rawSectionCocone)
open NativeAffineEtaleRawStageElements (chartMap stageAfterMap rawSection_map exists_representative)
open NativeAffineEtaleKanComparison (raw)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A : Type u} [CommRing A]

private abbrev R := CommRingCat.of A
private abbrev X := spectrum A
private abbrev G := AddCommGrpCat.{u + 1}

abbrev chart (U : Under (R (A := A))) [WeaklyEtale (Spec.map U.hom)] : (X (A := A)).ProEt :=
  Scheme.ProEt.mk (Spec.map U.hom)

abbrev arrow {U V : Under (R (A := A))}
    [WeaklyEtale (Spec.map U.hom)] [WeaklyEtale (Spec.map V.hom)] (f : U ⟶ V) : chart V ⟶ chart U :=
  MorphismProperty.Over.homMk (Spec.map f.right) (by
    change Spec.map f.right ≫ Spec.map U.hom = Spec.map V.hom
    rw [← Spec.map_comp, Under.w f])

theorem arrow_id (U : Under (R (A := A))) [WeaklyEtale (Spec.map U.hom)] :
    arrow (𝟙 U) = 𝟙 (chart U) := by
  apply MorphismProperty.Over.Hom.ext
  exact Spec.map_id _

theorem arrow_comp {U V W : Under (R (A := A))}
    [WeaklyEtale (Spec.map U.hom)] [WeaklyEtale (Spec.map V.hom)]
    [WeaklyEtale (Spec.map W.hom)] (a : U ⟶ V) (b : V ⟶ W) :
    arrow (a ≫ b) = arrow b ≫ arrow a := by
  apply MorphismProperty.Over.Hom.ext
  exact Spec.map_comp a.right b.right

variable (I : Sheaf (X (A := A)).smallEtaleTopology G.{u})

abbrev groups (U : Under (R (A := A))) [WeaklyEtale (Spec.map U.hom)] :=
  (raw (X (A := A)) I).obj (op (chart U))

abbrev restriction {U V : Under (R (A := A))}
    [WeaklyEtale (Spec.map U.hom)] [WeaklyEtale (Spec.map V.hom)] (f : U ⟶ V) :
    groups I U ⟶ groups I V :=
  (raw (X (A := A)) I).map (arrow f).op

abbrev represent {U : Under (R (A := A))} [WeaklyEtale (Spec.map U.hom)] (T : Stage A U) :=
  (rawSectionCocone (B := U) I).ι.app T

theorem restrict_repr {U V : Under (R (A := A))}
    [WeaklyEtale (Spec.map U.hom)] [WeaklyEtale (Spec.map V.hom)]
    (f : U ⟶ V) (T : Stage A U) (x : (sectionDiagram (B := U) I).obj T) :
    restriction I f (represent I T x) =
      represent I (stageAfterMap (CommRingCat.toAlgHom f) T) x :=
  DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom
    (rawSection_map I (CommRingCat.toAlgHom f) T)) x

variable {J : Type*} [Category* J] {D : J ⥤ Under (R (A := A))}
  (hT : ∀ j, WeaklyEtale (Spec.map (D.obj j).hom)) (c : Cocone D)

local instance (j : J) : WeaklyEtale (Spec.map (D.obj j).hom) := hT j

/-- Actual covariant restriction along the diagram of chart rings. -/
def diagram : J ⥤ G.{u} where
  obj j := groups I (D.obj j)
  map f := restriction I (D.map f)
  map_id j := by
    change (raw (X (A := A)) I).map (arrow (D.map (𝟙 j))).op = _
    rw [Functor.map_id, arrow_id, op_id, Functor.map_id]
  map_comp f g := by
    change (raw (X (A := A)) I).map (arrow (D.map (f ≫ g))).op = _
    rw [Functor.map_comp, arrow_comp, op_comp, Functor.map_comp] <;> rfl

variable [WeaklyEtale (Spec.map c.pt.hom)]

/-- The section cocone retains the literal geometric restriction maps. -/
def sectionCocone : Cocone (diagram I hT) where
  pt := groups I c.pt
  ι := { app := fun j ↦ restriction I (c.ι.app j)
         naturality := by
           intro i j f
           change restriction I (D.map f) ≫ restriction I (c.ι.app j) =
             restriction I (c.ι.app i) ≫ 𝟙 _
           rw [Category.comp_id]
           rw [show restriction I (D.map f) ≫ restriction I (c.ι.app j) =
               restriction I (D.map f ≫ c.ι.app j) by
                 change _ = (raw (X (A := A)) I).map (arrow (D.map f ≫ c.ι.app j)).op
                 rw [arrow_comp, op_comp, Functor.map_comp] <;> rfl, c.w] }

variable [IsFiltered J] [EssentiallySmall.{u} J]

set_option maxHeartbeats 5300000 in
/-- Each actual raw section at the affine limit comes from one diagram value. -/
theorem exists_section (hc : IsColimit c) (x : groups I c.pt) :
    ∃ (j : J) (y : groups I (D.obj j)), restriction I (c.ι.app j) y = x := by
  obtain ⟨T, z, hz⟩ := exists_representative I x
  let U := CommRingCat.mkUnder (R (A := A)) T.carrier
  have hU : U.hom.hom.FinitePresentation := RingHom.finitePresentation_algebraMap.mpr inferInstance
  obtain ⟨j, f, hf⟩ :=
    AffineStageFinitePresentationContinuity.exists_factorization U hc hU T.toChart.toUnder
  let S := Stage.of A (D.obj j) (algebraHom f)
  have h : (CommRingCat.toAlgHom (c.ι.app j)).comp S.toChart = T.toChart := by
    apply AlgHom.ext
    intro a
    exact congrArg (fun k : U ⟶ c.pt ↦ k.right a) hf
  let ev (g : T.carrier →ₐ[A] c.pt) := represent I (Stage.of A c.pt g) z
  have he : represent I (stageAfterMap (CommRingCat.toAlgHom (c.ι.app j)) S) z =
      represent I T z := congrArg ev h
  exact ⟨j, represent I S z, (restrict_repr I (c.ι.app j) S z).trans (he.trans hz)⟩

end
end ManuscriptAudit.NativeAffineUnderRingRawSections

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NativeAffineUnderRingRawSections.exists_section
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
