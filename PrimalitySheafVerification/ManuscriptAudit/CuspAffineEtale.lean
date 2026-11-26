import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import PrimalitySheafVerification.ManuscriptAudit.CuspEtaleHom

/-!
# The pullback functor of affine étale cusp schemes

The native pullback on the small étale categories, restricted to affine
objects, lands in the essential image of the affine étale site. This gives
a functor on the actual affine sites and identifies its map on homs.
-/

namespace ManuscriptAudit.CuspAffineEtale

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

variable (K : Type u) [Field K]

abbrev Cusp : Scheme.{u} := Spec (CommRingCat.of (CuspPunctured.CuspSubalgebra K))
abbrev Normalization : Scheme.{u} := Spec (CommRingCat.of (Polynomial K))

/-- The native base change on the small étale categories. -/
def etalePullback : (Cusp K).Etale ⥤ (Normalization K).Etale :=
  MorphismProperty.Over.pullback @AlgebraicGeometry.Etale.{u} ⊤ (CuspScheme.cuspMap K)

private abbrev toEtale : (Cusp K).AffineEtale ⥤ (Normalization K).Etale :=
  Scheme.AffineEtale.Spec (Cusp K) ⋙ etalePullback K

set_option backward.isDefEq.respectTransparency false in
private theorem toEtale_mem_affine (X : (Cusp K).AffineEtale) :
    (Scheme.AffineEtale.Spec (Normalization K)).essImage ((toEtale K).obj X) := by
  let Y := (toEtale K).obj X
  letI : IsAffine Y.left := by
    change IsAffine (pullback X.hom (CuspScheme.cuspMap K))
    infer_instance
  let e : Y.left ≅ Spec Γ(Y.left, ⊤) := Y.left.isoSpec
  let f : Spec Γ(Y.left, ⊤) ⟶ Normalization K := e.inv ≫ Y.hom
  letI : Etale f := by
    change Etale (e.inv ≫ Y.hom)
    infer_instance
  let Z := Scheme.AffineEtale.mk f
  refine ⟨Z, ⟨MorphismProperty.Over.isoMk e.symm ?_⟩⟩
  change e.inv ≫ Y.hom = f
  rfl

/-- Base change along cusp normalization in the native affine étale categories. -/
def affinePullback : (Cusp K).AffineEtale ⥤ (Normalization K).AffineEtale :=
  Functor.essImage.liftFunctor (toEtale K) (Scheme.AffineEtale.Spec (Normalization K))
    (toEtale_mem_affine K)

/-- The affine functor realizes the native scheme pullback along cusp normalization. -/
def affinePullbackSpecIso :
    affinePullback K ⋙ Scheme.AffineEtale.Spec (Normalization K) ≅
      Scheme.AffineEtale.Spec (Cusp K) ⋙ etalePullback K :=
  Functor.essImage.liftFunctorCompIso (toEtale K) (Scheme.AffineEtale.Spec (Normalization K))
    (toEtale_mem_affine K)

private abbrev affineOver (S : Scheme.{u}) : S.AffineEtale ⥤ Over S :=
  Scheme.AffineEtale.Spec S ⋙ Scheme.Etale.forget S

private abbrev overPullback : (Cusp K).AffineEtale ⥤ Over (Normalization K) :=
  affineOver (Cusp K) ⋙ Over.pullback (CuspScheme.cuspMap K)

private def etalePullbackForgetIso :
    toEtale K ⋙ Scheme.Etale.forget (Normalization K) ≅ overPullback K :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (MorphismProperty.Over.pullbackCompForgetIso
      (P := @AlgebraicGeometry.Etale.{u}) (Q := ⊤) (CuspScheme.cuspMap K)) ≪≫
    (Functor.associator _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
private theorem overPullback_map_bijective (X Y : (Cusp K).AffineEtale) :
    Function.Bijective ((overPullback K).map : (X ⟶ Y) → _) := by
  letI : Etale X.hom := X.prop
  letI : Etale Y.hom := Y.prop
  exact (CuspEtaleHom.overPullback_map_bijective K (unop X.left) (unop Y.left) X.hom Y.hom).comp
    ((Functor.FullyFaithful.ofFullyFaithful (affineOver (Cusp K))).map_bijective X Y)

/-- The actual pullback along cusp normalization is fully faithful on affine étale objects. -/
def affinePullbackFullyFaithful : (affinePullback K).FullyFaithful := by
  have h : Nonempty (overPullback K).FullyFaithful :=
    (Functor.FullyFaithful.nonempty_iff_map_bijective (overPullback K)).mpr
      (overPullback_map_bijective K)
  let hNative : (toEtale K).FullyFaithful :=
    Functor.FullyFaithful.ofCompFaithful
      ((Classical.choice h).ofIso (etalePullbackForgetIso K).symm)
  exact Functor.FullyFaithful.ofCompFaithful
    (hNative.ofIso (affinePullbackSpecIso K).symm)

/-- Pullback induces a bijection on each hom set of the native affine étale categories. -/
theorem affinePullback_map_bijective (X Y : (Cusp K).AffineEtale) :
    Function.Bijective ((affinePullback K).map : (X ⟶ Y) → _) :=
  (affinePullbackFullyFaithful K).map_bijective X Y

set_option backward.isDefEq.respectTransparency false in
/-- Actual affine étale descent squares imply essential surjectivity of the affine functor. -/
theorem affinePullback_essSurj_of_descent
    (h : ∀ (T : CommRingCat.{u}) (f : Spec T ⟶ Normalization K), Etale f →
      ∃ (R : CommRingCat.{u}) (d : Spec R ⟶ Cusp K), Etale d ∧
        ∃ j : Spec T ⟶ Spec R, IsPullback j f d (CuspScheme.cuspMap K)) :
    (affinePullback K).EssSurj where
  mem_essImage Y := by
    obtain ⟨R, d, hd, j, hj⟩ := h (unop Y.left) Y.hom Y.prop
    letI : Etale d := hd
    let X := Scheme.AffineEtale.mk d
    let e : (Scheme.AffineEtale.Spec (Normalization K)).obj Y ≅ (toEtale K).obj X :=
      MorphismProperty.Over.isoMk hj.isoPullback hj.isoPullback_hom_snd
    exact ⟨X, ⟨(Scheme.AffineEtale.Spec (Normalization K)).preimageIso
      ((affinePullbackSpecIso K).app X ≪≫ e.symm)⟩⟩

end

end ManuscriptAudit.CuspAffineEtale

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CuspAffineEtale.affinePullbackSpecIso,
      ``ManuscriptAudit.CuspAffineEtale.affinePullback_map_bijective,
      ``ManuscriptAudit.CuspAffineEtale.affinePullback_essSurj_of_descent] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
