import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Filtered.Final
import PrimalitySheafVerification.ManuscriptAudit.AffineStageFinitePresentationContinuity

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

private abbrev B := c.pt
private abbrev U (R : Type u) [CommRing R] [Algebra A R] :=
  CommRingCat.mkUnder (CommRingCat.of A) R

variable (hE : ∀ j, Etale (Spec.map (D.obj j).hom))

private def stage (j : J) : Stage A (B c) := by
  letI : Algebra.Etale A (D.obj j) := (RingHom.etale_algebraMap).mp
    ((HasRingHomProperty.Spec_iff (P := @Etale) (φ := (D.obj j).hom)).mp (hE j))
  exact Stage.of A (B c) (CommRingCat.toAlgHom (c.ι.app j))

/-- The chosen diagram gives actual étale stages of the chart ring. -/
def stageFunctor : J ⥤ Stage A (B c) where
  obj := stage c hE
  map {i j} f := ⟨CommRingCat.toAlgHom (D.map f), by
    change (CommRingCat.toAlgHom (c.ι.app j)).comp (CommRingCat.toAlgHom (D.map f)) =
      CommRingCat.toAlgHom (c.ι.app i)
    rw [← CommRingCat.toAlgHom_comp, c.w]⟩
  map_id j := by
    apply Subtype.ext
    change CommRingCat.toAlgHom (D.map (𝟙 j)) = _
    rw [Functor.map_id]
    rfl
  map_comp f g := by
    apply Subtype.ext
    change CommRingCat.toAlgHom (D.map (f ≫ g)) =
      (CommRingCat.toAlgHom (D.map g)).comp (CommRingCat.toAlgHom (D.map f))
    rw [Functor.map_comp, CommRingCat.toAlgHom_comp]

variable {c} {hE}

private def stageArrow (T : Stage A (B c)) {j : J}
    (v : U (A := A) T.carrier ⟶ D.obj j) (h : v ≫ c.ι.app j = T.toChart.toUnder) :
    T ⟶ (stageFunctor c hE).obj j :=
  ⟨CommRingCat.toAlgHom v, by
    change (CommRingCat.toAlgHom (c.ι.app j)).comp (CommRingCat.toAlgHom v) = T.toChart
    rw [← CommRingCat.toAlgHom_comp, h]
    apply AlgHom.ext
    intro _
    rfl⟩

private theorem finite (T : Stage A (B c)) :
    (U (A := A) T.carrier).hom.hom.FinitePresentation :=
  (RingHom.finitePresentation_algebraMap).mpr inferInstance

set_option maxHeartbeats 6200000 in
/-- The diagram's finality uses actual factorization and equality of
the ring maps into the same chart ring. -/
theorem final (hc : IsColimit c) : (stageFunctor c hE).Final where
  out T := by
    let F := stageFunctor c hE
    let P := U (A := A) T.carrier
    let v := T.toChart.toUnder
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
        let a : P ⟶ D.obj q := (hom X.hom).toUnder ≫ D.map i
        let b : P ⟶ D.obj q := (hom Y.hom).toUnder ≫ D.map j
        have ha : a ≫ c.ι.app q = v := by
          change ((hom X.hom).toUnder ≫ D.map i) ≫ c.ι.app q = v
          rw [Category.assoc, c.w, ← AlgHom.toUnder_comp]
          exact congrArg AlgHom.toUnder X.hom.property
        have hb : b ≫ c.ι.app q = v := by
          change ((hom Y.hom).toUnder ≫ D.map j) ≫ c.ι.app q = v
          rw [Category.assoc, c.w, ← AlgHom.toUnder_comp]
          exact congrArg AlgHom.toUnder Y.hom.property
        obtain ⟨l, k, hk⟩ := exists_equalizer P hc hP a b (ha.trans hb.symm)
        have h₁ : (a ≫ D.map k) ≫ c.ι.app l = v := by
          rw [Category.assoc, c.w, ha]
        let Z : StructuredArrow T F := StructuredArrow.mk (stageArrow (hE := hE) T (a ≫ D.map k) h₁)
        refine ⟨Z, StructuredArrow.homMk (i ≫ k) ?_, StructuredArrow.homMk (j ≫ k) ?_, trivial⟩
        · apply Subtype.ext
          change (CommRingCat.toAlgHom (D.map (i ≫ k))).comp (hom X.hom) =
            CommRingCat.toAlgHom (a ≫ D.map k)
          rw [Functor.map_comp, CommRingCat.toAlgHom_comp, CommRingCat.toAlgHom_comp,
            CommRingCat.toAlgHom_comp]
          rfl
        · apply Subtype.ext
          change (CommRingCat.toAlgHom (D.map (j ≫ k))).comp (hom Y.hom) =
            CommRingCat.toAlgHom (a ≫ D.map k)
          rw [hk, Functor.map_comp, CommRingCat.toAlgHom_comp, CommRingCat.toAlgHom_comp,
            CommRingCat.toAlgHom_comp]
          rfl
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
