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

abbrev chartAlgebra (B : Under (R (A := A))) : Algebra A B.right := B.hom.hom.toAlgebra

attribute [local instance] chartAlgebra

/-- Read a chart-ring map using the actual algebra structures from its arrows. -/
abbrev chartRingHom {U V : Under (R (A := A))} (f : U ⟶ V) : U.right →ₐ[A] V.right :=
  { toRingHom := f.right.hom
    commutes' := fun x ↦ congrArg (fun g : R (A := A) ⟶ V.right ↦ g x) (Under.w f) }

local instance chartWeaklyEtale (U : Under (R (A := A)))
    [WeaklyEtale (Spec.map U.hom)] : WeaklyEtale (structureMap A U.right) :=
  inferInstanceAs (WeaklyEtale (Spec.map U.hom))

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

abbrev represent {U : Under (R (A := A))} [WeaklyEtale (Spec.map U.hom)] (T : Stage A U.right) :=
  (rawSectionCocone (B := U.right) I).ι.app T

theorem restrict_repr {U V : Under (R (A := A))}
    [WeaklyEtale (Spec.map U.hom)] [WeaklyEtale (Spec.map V.hom)]
    (f : U ⟶ V) (T : Stage A U.right) (x : (sectionDiagram (B := U.right) I).obj T) :
    restriction I f (represent I T x) =
      represent I (stageAfterMap (chartRingHom f) T) x :=
  DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom
    (rawSection_map I (chartRingHom f) T)) x

variable {J : Type*} [Category* J] {D : J ⥤ Under (R (A := A))}
  (hT : ∀ j, WeaklyEtale (Spec.map (D.obj j).hom)) (c : Cocone D)

/-- Actual covariant restriction along the diagram of chart rings. -/
def diagram : J ⥤ G.{u} where
  obj j := @groups _ _ I (D.obj j) (hT j)
  map {i j} f := @restriction _ _ I (D.obj i) (D.obj j) (hT i) (hT j) (D.map f)
  map_id j := by
    letI : WeaklyEtale (Spec.map (D.obj j).hom) := hT j
    change (raw (X (A := A)) I).map (arrow (D.map (𝟙 j))).op = _
    rw [CategoryTheory.Functor.map_id, arrow_id, op_id, CategoryTheory.Functor.map_id]
  map_comp {i j k} f g := by
    letI : WeaklyEtale (Spec.map (D.obj i).hom) := hT i
    letI : WeaklyEtale (Spec.map (D.obj j).hom) := hT j
    letI : WeaklyEtale (Spec.map (D.obj k).hom) := hT k
    change (raw (X (A := A)) I).map (arrow (D.map (f ≫ g))).op = _
    rw [CategoryTheory.Functor.map_comp, arrow_comp, op_comp, CategoryTheory.Functor.map_comp] <;> rfl

variable [hC : WeaklyEtale (Spec.map c.pt.hom)]

private abbrev leg (j : J) : D.obj j ⟶ c.pt := c.ι.app j

/-- The section cocone retains the literal geometric restriction maps. -/
def sectionCocone : Cocone (diagram I hT) where
  pt := groups I c.pt
  ι := { app := fun j ↦ @restriction _ _ I (D.obj j) c.pt (hT j) hC (leg c j)
         naturality := by
           intro i j f
           letI : WeaklyEtale (Spec.map (D.obj i).hom) := hT i
           letI : WeaklyEtale (Spec.map (D.obj j).hom) := hT j
           change restriction I (D.map f) ≫ restriction I (leg c j) =
             restriction I (leg c i) ≫ 𝟙 _
           rw [Category.comp_id]
           have h : D.map f ≫ leg c j = leg c i := c.w f
           calc
             _ = restriction I (D.map f ≫ leg c j) := by
               change _ = (raw (X (A := A)) I).map (arrow (D.map f ≫ leg c j)).op
               rw [arrow_comp, op_comp, CategoryTheory.Functor.map_comp] <;> rfl
             _ = _ := congrArg (restriction I) h }

variable [IsFiltered J] [EssentiallySmall.{u} J]

set_option maxHeartbeats 5300000 in
/-- Each actual raw section at the affine limit comes from one diagram value. -/
theorem exists_section (hc : IsColimit c) (x : groups I c.pt) :
    ∃ (j : J) (y : @groups _ _ I (D.obj j) (hT j)),
      @restriction _ _ I (D.obj j) c.pt (hT j) hC (leg c j) y = x := by
  obtain ⟨T, z, hz⟩ := exists_representative (B := c.pt.right) I x
  letI : Algebra A T.carrier := T.algebra
  letI : Algebra.Etale A T.carrier := T.isEtale
  let U := CommRingCat.mkUnder (R (A := A)) T.carrier
  have hU : U.hom.hom.FinitePresentation := by
    change (algebraMap A T.carrier).FinitePresentation
    exact RingHom.finitePresentation_algebraMap.mpr inferInstance
  obtain ⟨j, f, hf⟩ :=
    AffineStageFinitePresentationContinuity.exists_factorization U hc hU T.toChart.toUnder
  letI : WeaklyEtale (Spec.map (D.obj j).hom) := hT j
  let f₀ : T.carrier →ₐ[A] (D.obj j).right := algebraHom f
  let S := Stage.of A (D.obj j).right f₀
  have h : (chartRingHom (leg c j)).comp f₀ = T.toChart := by
    apply AlgHom.ext
    intro a
    exact congrArg (fun k : U ⟶ c.pt ↦ k.right a) hf
  let ev (g : T.carrier →ₐ[A] c.pt.right) : groups I c.pt :=
    represent I (Stage.of A c.pt.right g) z
  have he : represent I (stageAfterMap (chartRingHom (leg c j)) S) z =
      represent I T z := by
    change ev ((chartRingHom (leg c j)).comp f₀) = ev T.toChart
    exact congrArg ev h
  exact ⟨j, represent I S z, (restrict_repr I (leg c j) S z).trans (he.trans hz)⟩

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
