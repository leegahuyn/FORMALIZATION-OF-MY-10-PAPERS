import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Filtered.Final
import PrimalitySheafVerification.ManuscriptAudit.AffineStageFinitePresentationContinuity
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleStageAlgebraColimit

/-! A filtered diagram of affine étale rings with the actual chart as
its colimit is final among all genuine affine étale stages of that chart. -/

namespace ManuscriptAudit.AffineEtaleStageCofinalDiagram

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AffineEtaleStageCategory (Stage hom)
open AffineStageFinitePresentationContinuity (exists_factorization exists_equalizer)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A : Type u} [CommRing A]
  {J : Type*} [Category* J] [IsFiltered J] [EssentiallySmall.{u} J]
  {D : J ⥤ Under (CommRingCat.of A)} (c : Cocone D)

private abbrev R := CommRingCat.of A

local instance chartAlgebra (P : Under (R (A := A))) : Algebra A P.right :=
  P.hom.hom.toAlgebra

private abbrev U (R : Type u) [CommRing R] [Algebra A R] :=
  CommRingCat.mkUnder (CommRingCat.of A) R

private abbrev ringMap {P Q : Under (R (A := A))} (a : P ⟶ Q) : P.right →ₐ[A] Q.right :=
  { toRingHom := a.right.hom
    commutes' := fun x ↦ congrArg (fun t : R (A := A) ⟶ Q.right ↦ t x) (Under.w a) }

private abbrev leg (j : J) : D.obj j ⟶ c.pt := c.ι.app j

variable (hE : ∀ j, Etale (Spec.map (D.obj j).hom))

private def stage (j : J) : Stage A c.pt.right := by
  have h : (algebraMap A (D.obj j).right).Etale :=
    (HasRingHomProperty.Spec_iff (P := @Etale) (φ := (D.obj j).hom)).mp (hE j)
  letI : Algebra.Etale A (D.obj j).right := (RingHom.etale_algebraMap).mp h
  exact Stage.of A c.pt.right (ringMap (leg c j))

/-- The chosen diagram gives actual étale stages of the chart ring. -/
def stageFunctor : J ⥤ Stage A c.pt.right where
  obj := stage c hE
  map {i j} f := ⟨ringMap (D.map f), by
    apply AlgHom.ext
    intro x
    exact congrArg (fun a : D.obj i ⟶ c.pt ↦ a.right x) (c.w f)⟩
  map_id j := by
    apply Subtype.ext
    apply AlgHom.ext
    intro x
    exact congrArg (fun a : D.obj j ⟶ D.obj j ↦ a.right x) (D.map_id j)
  map_comp f g := by
    apply Subtype.ext
    apply AlgHom.ext
    intro x
    exact congrArg (fun a : D.obj _ ⟶ D.obj _ ↦ a.right x) (D.map_comp f g)

variable {c} {hE}

private def stageArrow (T : Stage A c.pt.right) {j : J}
    (v : U (A := A) T.carrier ⟶ D.obj j) (h : v ≫ leg c j = T.toChart.toUnder) :
    T ⟶ (stageFunctor c hE).obj j :=
  ⟨{ toRingHom := v.right.hom
     commutes' := fun x ↦ congrArg (fun a : R (A := A) ⟶ (D.obj j).right ↦ a x) (Under.w v) },
    by
      apply AlgHom.ext
      intro x
      exact congrArg (fun a : U (A := A) T.carrier ⟶ c.pt ↦ a.right x) h⟩

private def pointMap {T : Stage A c.pt.right} (s : StructuredArrow T (stageFunctor c hE)) :
    U (A := A) T.carrier ⟶ D.obj s.right :=
  Under.homMk (CommRingCat.ofHom (hom s.hom).toRingHom) (by
    apply CommRingCat.hom_ext
    ext x
    exact (hom s.hom).commutes x)

private theorem pointMap_comp {T : Stage A c.pt.right} (s : StructuredArrow T (stageFunctor c hE)) :
    pointMap s ≫ leg c s.right = T.toChart.toUnder := by
  apply (Under.forget (CommRingCat.of A)).map_injective
  apply CommRingCat.hom_ext
  ext x
  exact DFunLike.congr_fun s.hom.property x

private theorem finite (T : Stage A c.pt.right) :
    (U (A := A) T.carrier).hom.hom.FinitePresentation := by
  letI : Algebra A T.carrier := T.algebra
  letI : Algebra.Etale A T.carrier := T.isEtale
  change (algebraMap A T.carrier).FinitePresentation
  exact RingHom.finitePresentation_algebraMap.mpr inferInstance

set_option maxHeartbeats 6200000 in
/-- The diagram's finality uses actual factorization and equality of
the ring maps into the same chart ring. -/
theorem final (hc : IsColimit c) : (stageFunctor c hE).Final where
  out T := by
    let F := stageFunctor c hE
    letI : Algebra A T.carrier := T.algebra
    let P := U (A := A) T.carrier
    let v : P ⟶ c.pt := T.toChart.toUnder
    have hP : P.hom.hom.FinitePresentation := finite T
    let hFilt : IsFiltered (StructuredArrow T F) := {
      nonempty := by
        obtain ⟨j, w, hw⟩ := exists_factorization P hc hP v
        exact ⟨StructuredArrow.mk (stageArrow (hE := hE) T w hw)⟩
      cocone_objs := by
        intro X Y
        let q := IsFiltered.max X.right Y.right
        let i := IsFiltered.leftToMax X.right Y.right
        let j := IsFiltered.rightToMax X.right Y.right
        let a : P ⟶ D.obj q := pointMap X ≫ D.map i
        let b : P ⟶ D.obj q := pointMap Y ≫ D.map j
        have ha : a ≫ leg c q = v := by
          simp only [a, leg, Category.assoc, c.w]
          exact pointMap_comp X
        have hb : b ≫ leg c q = v := by
          simp only [b, leg, Category.assoc, c.w]
          exact pointMap_comp Y
        obtain ⟨l, k, hk⟩ := exists_equalizer P hc hP a b (ha.trans hb.symm)
        have h₁ : (a ≫ D.map k) ≫ leg c l = v := by
          simp only [leg, Category.assoc, c.w]
          exact ha
        let Z : StructuredArrow T F := StructuredArrow.mk (stageArrow (hE := hE) T (a ≫ D.map k) h₁)
        refine ⟨Z, StructuredArrow.homMk (i ≫ k) ?_, StructuredArrow.homMk (j ≫ k) ?_, trivial⟩
        · apply Subtype.ext
          apply AlgHom.ext
          intro x
          have h : pointMap X ≫ D.map (i ≫ k) = a ≫ D.map k := by
            simp only [a, D.map_comp, Category.assoc]
          exact congrArg (fun t : P ⟶ D.obj l ↦ t.right x) h
        · apply Subtype.ext
          apply AlgHom.ext
          intro x
          have h : pointMap Y ≫ D.map (j ≫ k) = a ≫ D.map k := by
            simp only [b, D.map_comp, Category.assoc] at hk ⊢
            exact hk.symm
          exact congrArg (fun t : P ⟶ D.obj l ↦ t.right x) h
      cocone_maps := by
        intro X Y a b
        let j := IsFiltered.coeq a.right b.right
        let k := IsFiltered.coeqHom a.right b.right
        let Z : StructuredArrow T F := StructuredArrow.mk (Y.hom ≫ F.map k)
        refine ⟨Z, StructuredArrow.homMk k rfl, ?_⟩
        apply StructuredArrow.hom_ext
        exact IsFiltered.coeq_condition a.right b.right }
    letI := hFilt
    exact IsFiltered.isConnected _

end
end ManuscriptAudit.AffineEtaleStageCofinalDiagram

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineEtaleStageCofinalDiagram.final
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
