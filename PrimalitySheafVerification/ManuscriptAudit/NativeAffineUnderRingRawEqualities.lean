import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NativeAffineUnderRingRawSections
import PrimalitySheafVerification.ManuscriptAudit.AffineStageSimultaneousEqualities

/-! An equality of actual raw sections at an affine filtered limit
already holds after one genuine forward restriction. -/

namespace ManuscriptAudit.NativeAffineUnderRingRawEqualities

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AffineEtaleStageCategory (Stage hom)
open AffineEtaleStageTensorLegs (algebraHom)
open NativeAffineEtaleStageSections (sectionDiagram)
open NativeAffineEtaleRawSections (rawSectionCocone)
open NativeAffineEtaleRawStageElements (stageAfterMap exists_representative exists_equal_representatives)
open NativeAffineUnderRingRawSections (groups restriction represent restrict_repr)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A : Type u} [CommRing A]

private abbrev R := CommRingCat.of A
private abbrev U (S : Type u) [CommRing S] [Algebra A S] := CommRingCat.mkUnder (R (A := A)) S
private abbrev X := ProetaleAffineTensor.spectrum A
private abbrev G := AddCommGrpCat.{u + 1}

variable (I : Sheaf (X (A := A)).smallEtaleTopology G.{u})

private theorem repr_natural {B : Under (R (A := A))} [WeaklyEtale (Spec.map B.hom)]
    {T V : Stage A B} (e : T ⟶ V) (x : (sectionDiagram (B := B) I).obj T) :
    represent I V ((sectionDiagram (B := B) I).map e x) = represent I T x :=
  DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom
    ((rawSectionCocone (B := B) I).w e)) x

variable {J : Type*} [Category* J] [IsFiltered J] [EssentiallySmall.{u} J]
  {D : J ⥤ Under (R (A := A))}
  (hT : ∀ j, WeaklyEtale (Spec.map (D.obj j).hom)) {c : Cocone D}
  [WeaklyEtale (Spec.map c.pt.hom)]

local instance (i : J) : WeaklyEtale (Spec.map (D.obj i).hom) := hT i

set_option maxHeartbeats 10500000 in
/-- A raw equality at the actual colimit is witnessed at one later
chart ring in the specified diagram. -/
theorem exists_equal_stage (hc : IsColimit c) (i : J)
    (x y : groups I (D.obj i))
    (hxy : restriction I (c.ι.app i) x = restriction I (c.ι.app i) y) :
    ∃ (j : J) (e : i ⟶ j), restriction I (D.map e) x = restriction I (D.map e) y := by
  obtain ⟨T, u, hu⟩ := exists_representative I x
  obtain ⟨V, v, hv⟩ := exists_representative I y
  let k := CommRingCat.toAlgHom (c.ι.app i)
  let T' := stageAfterMap k T
  let V' := stageAfterMap k V
  have hEq : represent I T' u = represent I V' v := by
    rw [← restrict_repr, ← restrict_repr, hu, hv]
    exact hxy
  obtain ⟨N, p, q, hz⟩ := exists_equal_representatives I T' V' u v hEq
  let P := U (A := A) T.carrier
  let Q := U (A := A) V.carrier
  let E := U (A := A) N.carrier
  have hP : P.hom.hom.FinitePresentation := RingHom.finitePresentation_algebraMap.mpr inferInstance
  have hQ : Q.hom.hom.FinitePresentation := RingHom.finitePresentation_algebraMap.mpr inferInstance
  have hE : E.hom.hom.FinitePresentation := RingHom.finitePresentation_algebraMap.mpr inferInstance
  obtain ⟨j, w, hw⟩ := AffineStageFinitePresentationContinuity.exists_factorization E hc hE N.toChart.toUnder
  have hp : T.toChart.toUnder ≫ c.ι.app i = (hom p).toUnder ≫ N.toChart.toUnder := by
    apply (Under.forget (R (A := A))).map_injective
    apply CommRingCat.hom_ext
    ext t
    exact (DFunLike.congr_fun p.property t).symm
  have hq : V.toChart.toUnder ≫ c.ι.app i = (hom q).toUnder ≫ N.toChart.toUnder := by
    apply (Under.forget (R (A := A))).map_injective
    apply CommRingCat.hom_ext
    ext t
    exact (DFunLike.congr_fun q.property t).symm
  let l := IsFiltered.max i j
  let il := IsFiltered.leftToMax i j
  let jl := IsFiltered.rightToMax i j
  let p₁ : P ⟶ D.obj l := T.toChart.toUnder ≫ D.map il
  let p₂ : P ⟶ D.obj l := (hom p).toUnder ≫ w ≫ D.map jl
  let q₁ : Q ⟶ D.obj l := V.toChart.toUnder ≫ D.map il
  let q₂ : Q ⟶ D.obj l := (hom q).toUnder ≫ w ≫ D.map jl
  have h₁ : p₁ ≫ c.ι.app l = p₂ ≫ c.ι.app l := by
    simpa only [p₁, p₂, Category.assoc, c.w, hw] using hp
  have h₂ : q₁ ≫ c.ι.app l = q₂ ≫ c.ι.app l := by
    simpa only [q₁, q₂, Category.assoc, c.w, hw] using hq
  obtain ⟨m, lm, hmP, hmQ⟩ :=
    AffineStageSimultaneousEqualities.exists_two_equalizers hc P Q hP hQ p₁ p₂ q₁ q₂ h₁ h₂
  let im := il ≫ lm
  let jm := jl ≫ lm
  let W := Stage.of A (D.obj m) (algebraHom (w ≫ D.map jm))
  have h₁' : T.toChart.toUnder ≫ D.map im = (hom p).toUnder ≫ w ≫ D.map jm := by
    simpa only [p₁, p₂, im, jm, Functor.map_comp, Category.assoc] using hmP
  have h₂' : V.toChart.toUnder ≫ D.map im = (hom q).toUnder ≫ w ≫ D.map jm := by
    simpa only [q₁, q₂, im, jm, Functor.map_comp, Category.assoc] using hmQ
  let p' : stageAfterMap (CommRingCat.toAlgHom (D.map im)) T ⟶ W := ⟨hom p, by
    apply AlgHom.ext
    intro t
    exact congrArg (fun a : P ⟶ D.obj m ↦ a.right t) h₁'.symm⟩
  let q' : stageAfterMap (CommRingCat.toAlgHom (D.map im)) V ⟶ W := ⟨hom q, by
    apply AlgHom.ext
    intro t
    exact congrArg (fun a : Q ⟶ D.obj m ↦ a.right t) h₂'.symm⟩
  refine ⟨m, im, ?_⟩
  rw [← hu, ← hv, restrict_repr, restrict_repr]
  exact (repr_natural I p' u).symm.trans
    ((congrArg (represent I W) hz).trans (repr_natural I q' v))

end
end ManuscriptAudit.NativeAffineUnderRingRawEqualities

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NativeAffineUnderRingRawEqualities.exists_equal_stage
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
