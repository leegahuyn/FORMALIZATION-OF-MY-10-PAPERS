import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineProetaleSite
import PrimalitySheafVerification.ManuscriptAudit.CuspProetaleAffineDescent
import PrimalitySheafVerification.ManuscriptAudit.CuspWeaklyEtaleHom

/-! Actual base change along the cusp normalization is fully faithful
on affine weakly étale schemes, and is an equivalence in prime characteristic. -/

namespace ManuscriptAudit.CuspProetaleAffineEquivalence

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AffineProetaleSite (Affine affineObjects inclusion specIso)

universe u

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private def homCongr {C : Type*} [Category* C] {U V U' V' : C} (e : U ≅ U') (f : V ≅ V') :
    (U ⟶ V) ≃ (U' ⟶ V') where
  toFun h := e.inv ≫ h ≫ f.hom
  invFun h := e.hom ≫ h ≫ f.inv
  left_inv h := by simp
  right_inv h := by simp

private theorem map_bijective_of_iso {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {U V U' V' : C} (e : U ≅ U') (f : V ≅ V')
    (h : Function.Bijective (F.map : (U' ⟶ V') → _)) : Function.Bijective (F.map : (U ⟶ V) → _) := by
  let a := homCongr e f
  let b := homCongr (F.mapIso e) (F.mapIso f)
  have w (t : U ⟶ V) : b (F.map t) = F.map (a t) := by
    change (F.mapIso e).inv ≫ F.map t ≫ (F.mapIso f).hom = F.map (e.inv ≫ t ≫ f.hom)
    simp only [Functor.map_comp, Functor.mapIso_inv, Functor.mapIso_hom]
  constructor
  · intro x y hxy
    apply a.injective
    apply h.injective
    rw [← w, ← w, hxy]
  · intro y
    obtain ⟨z, hz⟩ := h.surjective (b y)
    obtain ⟨x, hx⟩ := a.surjective z
    refine ⟨x, b.injective ?_⟩
    rw [w, hx, hz]

variable (K : Type u) [Field K]

abbrev Cusp := Spec (CommRingCat.of (CuspPunctured.CuspSubalgebra K))
abbrev Normalization := Spec (CommRingCat.of (Polynomial K))

/-- The actual pullback functor of affine native weakly étale charts. -/
abbrev normalizationPullback : Affine (Cusp K) ⥤ Affine (Normalization K) :=
  AffineProetaleSite.baseChange (CuspScheme.cuspMap K)

private abbrev toOver (X : Scheme.{u}) : Affine X ⥤ Over X :=
  inclusion X ⋙ Scheme.ProEt.forget X

private abbrev overPullback : Affine (Cusp K) ⥤ Over (Normalization K) :=
  toOver (Cusp K) ⋙ Over.pullback (CuspScheme.cuspMap K)

private theorem overPullback_map_bijective (U V : Affine (Cusp K)) :
    Function.Bijective ((overPullback K).map : (U ⟶ V) → _) := by
  letI : IsAffine U.obj.left := U.property
  letI : IsAffine V.obj.left := V.property
  letI : WeaklyEtale U.obj.hom := U.obj.prop
  letI : WeaklyEtale V.obj.hom := V.obj.prop
  let f := U.obj.left.isoSpec.inv ≫ U.obj.hom
  let g := V.obj.left.isoSpec.inv ≫ V.obj.hom
  letI : WeaklyEtale f := inferInstanceAs (WeaklyEtale (U.obj.left.isoSpec.inv ≫ U.obj.hom))
  letI : WeaklyEtale g := inferInstanceAs (WeaklyEtale (V.obj.left.isoSpec.inv ≫ V.obj.hom))
  apply map_bijective_of_iso (overPullback K) (specIso (Cusp K) U) (specIso (Cusp K) V)
  exact (CuspWeaklyEtaleHom.overPullback_map_bijective K _ _ f g).comp
    ((Functor.FullyFaithful.ofFullyFaithful (toOver (Cusp K))).map_bijective
      (AffineProetaleSite.mk (Cusp K) f) (AffineProetaleSite.mk (Cusp K) g))

/-- Full faithfulness of the actual affine weakly étale pullback along cusp normalization. -/
def normalizationFullyFaithful : (normalizationPullback K).FullyFaithful := by
  let e : normalizationPullback K ⋙ toOver (Normalization K) ≅ overPullback K := Iso.refl _
  have h : Nonempty (overPullback K).FullyFaithful :=
    (Functor.FullyFaithful.nonempty_iff_map_bijective (overPullback K)).mpr (overPullback_map_bijective K)
  exact Functor.FullyFaithful.ofCompFaithful ((Classical.choice h).ofIso e.symm)

variable (p : ℕ) [pPrime : Fact p.Prime] [kCharP : CharP K p]

include p pPrime kCharP in
/-- Every actual affine weakly étale chart over the normalization descends in prime characteristic. -/
theorem normalizationEssSurj : (normalizationPullback K).EssSurj where
  mem_essImage U := by
    letI : IsAffine U.obj.left := U.property
    letI : WeaklyEtale U.obj.hom := U.obj.prop
    let f := U.obj.left.isoSpec.inv ≫ U.obj.hom
    letI : WeaklyEtale f := inferInstanceAs (WeaklyEtale (U.obj.left.isoSpec.inv ≫ U.obj.hom))
    let e := specIso (Normalization K) U
    obtain ⟨R, d, hd, a, ha⟩ := CuspProetaleAffineDescent.affine_weaklyEtale_descends K p _ f
    letI : WeaklyEtale d := hd
    let W := AffineProetaleSite.mk (Cusp K) d
    let e' : (AffineProetaleSite.mk (Normalization K) f).obj ≅
        ((normalizationPullback K).obj W).obj :=
      MorphismProperty.Over.isoMk ha.isoPullback ha.isoPullback_hom_snd
    let h := (affineObjects (Normalization K)).fullyFaithfulι.preimageIso e'
    exact ⟨W, ⟨h.symm ≪≫ e.symm⟩⟩

include p pPrime kCharP in
theorem normalizationIsEquivalence : (normalizationPullback K).IsEquivalence where
  full := (normalizationFullyFaithful K).full
  faithful := (normalizationFullyFaithful K).faithful
  essSurj := normalizationEssSurj K p

/-- The actual affine pro-étale normalization equivalence in prime characteristic. -/
def normalizationEquivalence : Affine (Cusp K) ≌ Affine (Normalization K) :=
  letI := normalizationIsEquivalence K p
  (normalizationPullback K).asEquivalence

end
end ManuscriptAudit.CuspProetaleAffineEquivalence

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CuspProetaleAffineEquivalence.normalizationFullyFaithful,
      ``ManuscriptAudit.CuspProetaleAffineEquivalence.normalizationEssSurj,
      ``ManuscriptAudit.CuspProetaleAffineEquivalence.normalizationEquivalence] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
