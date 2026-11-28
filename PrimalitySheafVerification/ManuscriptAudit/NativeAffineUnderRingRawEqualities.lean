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
open NativeAffineUnderRingRawSections (groups restriction represent restrict_repr chartAlgebra chartRingHom)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A : Type u} [CommRing A]

private abbrev R := CommRingCat.of A
private abbrev U (S : Type u) [CommRing S] [Algebra A S] := CommRingCat.mkUnder (R (A := A)) S
private abbrev X := ProetaleAffineTensor.spectrum A
private abbrev G := AddCommGrpCat.{u + 1}

attribute [local instance] chartAlgebra

variable (I : Sheaf (X (A := A)).smallEtaleTopology G.{u})

private theorem repr_natural {B : Under (R (A := A))} [WeaklyEtale (Spec.map B.hom)]
    {T V : Stage A B.right} (e : T ⟶ V) (x : (sectionDiagram (B := B.right) I).obj T) :
    represent I V ((sectionDiagram (B := B.right) I).map e x) = represent I T x := by
  letI : WeaklyEtale (ProetaleAffineTensor.structureMap A B.right) :=
    inferInstanceAs (WeaklyEtale (Spec.map B.hom))
  exact DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom
    ((rawSectionCocone (B := B.right) I).w e)) x

variable {J : Type*} [Category* J] [IsFiltered J] [EssentiallySmall.{u} J]
  {D : J ⥤ Under (R (A := A))}
  (hT : ∀ j, WeaklyEtale (Spec.map (D.obj j).hom)) {c : Cocone D}
  [hC : WeaklyEtale (Spec.map c.pt.hom)]

private abbrev leg (j : J) : D.obj j ⟶ c.pt := c.ι.app j

set_option maxHeartbeats 10500000 in
/-- A raw equality at the actual colimit is witnessed at one later
chart ring in the specified diagram. -/
theorem exists_equal_stage (hc : IsColimit c) (i : J)
    (x y : @groups _ _ I (D.obj i) (hT i))
    (hxy : @restriction _ _ I (D.obj i) c.pt (hT i) hC (leg c i) x =
      @restriction _ _ I (D.obj i) c.pt (hT i) hC (leg c i) y) :
    ∃ (j : J) (e : i ⟶ j), @restriction _ _ I (D.obj i) (D.obj j) (hT i) (hT j) (D.map e) x =
      @restriction _ _ I (D.obj i) (D.obj j) (hT i) (hT j) (D.map e) y := by
  letI : WeaklyEtale (Spec.map (D.obj i).hom) := hT i
  letI : WeaklyEtale (ProetaleAffineTensor.structureMap A (D.obj i).right) := hT i
  letI : WeaklyEtale (ProetaleAffineTensor.structureMap A c.pt.right) := hC
  obtain ⟨T, u, hu⟩ := exists_representative (B := (D.obj i).right) I x
  obtain ⟨V, v, hv⟩ := exists_representative (B := (D.obj i).right) I y
  let k := chartRingHom (leg c i)
  let T' := stageAfterMap k T
  let V' := stageAfterMap k V
  have hEq : represent I T' u = represent I V' v := calc
    _ = restriction I (leg c i) (represent I T u) := (restrict_repr I (leg c i) T u).symm
    _ = restriction I (leg c i) x := congrArg (restriction I (leg c i)) hu
    _ = restriction I (leg c i) y := hxy
    _ = restriction I (leg c i) (represent I V v) := congrArg (restriction I (leg c i)) hv.symm
    _ = _ := restrict_repr I (leg c i) V v
  obtain ⟨N, p, q, hz⟩ := exists_equal_representatives I T' V' u v hEq
  let P := U (A := A) T.carrier
  let Q := U (A := A) V.carrier
  let E := U (A := A) N.carrier
  have hP : P.hom.hom.FinitePresentation := by
    letI : Algebra A T.carrier := T.algebra
    letI : Algebra.Etale A T.carrier := T.isEtale
    change (algebraMap A T.carrier).FinitePresentation
    exact RingHom.finitePresentation_algebraMap.mpr inferInstance
  have hQ : Q.hom.hom.FinitePresentation := by
    letI : Algebra A V.carrier := V.algebra
    letI : Algebra.Etale A V.carrier := V.isEtale
    change (algebraMap A V.carrier).FinitePresentation
    exact RingHom.finitePresentation_algebraMap.mpr inferInstance
  have hE : E.hom.hom.FinitePresentation := by
    letI : Algebra A N.carrier := N.algebra
    letI : Algebra.Etale A N.carrier := N.isEtale
    change (algebraMap A N.carrier).FinitePresentation
    exact RingHom.finitePresentation_algebraMap.mpr inferInstance
  obtain ⟨j, w, hw⟩ := AffineStageFinitePresentationContinuity.exists_factorization E hc hE N.toChart.toUnder
  have hp : T.toChart.toUnder ≫ leg c i = (hom p).toUnder ≫ N.toChart.toUnder := by
    apply (Under.forget (R (A := A))).map_injective
    apply CommRingCat.hom_ext
    ext t
    exact (DFunLike.congr_fun p.property t).symm
  have hq : V.toChart.toUnder ≫ leg c i = (hom q).toUnder ≫ N.toChart.toUnder := by
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
    simpa only [p₁, p₂, leg, Category.assoc, c.w, hw] using hp
  have h₂ : q₁ ≫ c.ι.app l = q₂ ≫ c.ι.app l := by
    simpa only [q₁, q₂, leg, Category.assoc, c.w, hw] using hq
  obtain ⟨m, lm, hmP, hmQ⟩ :=
    AffineStageSimultaneousEqualities.exists_two_equalizers hc P Q hP hQ p₁ p₂ q₁ q₂ h₁ h₂
  let im := il ≫ lm
  let jm := jl ≫ lm
  letI : WeaklyEtale (Spec.map (D.obj m).hom) := hT m
  let W := Stage.of A (D.obj m).right (algebraHom (w ≫ D.map jm))
  have h₁' : T.toChart.toUnder ≫ D.map im = (hom p).toUnder ≫ w ≫ D.map jm := by
    simpa only [p₁, p₂, im, jm, CategoryTheory.Functor.map_comp, Category.assoc] using hmP
  have h₂' : V.toChart.toUnder ≫ D.map im = (hom q).toUnder ≫ w ≫ D.map jm := by
    simpa only [q₁, q₂, im, jm, CategoryTheory.Functor.map_comp, Category.assoc] using hmQ
  let p' : stageAfterMap (chartRingHom (D.map im)) T ⟶ W := ⟨hom p, by
    apply AlgHom.ext
    intro t
    exact congrArg (fun a : P ⟶ D.obj m ↦ a.right t) h₁'.symm⟩
  let q' : stageAfterMap (chartRingHom (D.map im)) V ⟶ W := ⟨hom q, by
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
