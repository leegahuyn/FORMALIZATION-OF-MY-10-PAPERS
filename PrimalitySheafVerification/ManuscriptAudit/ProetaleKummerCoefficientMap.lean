import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleKummerRoots

/-! Constant coefficient roots restrict to actual regular-function
roots on every object, with explicit compatibility on affine spectra. -/

namespace ManuscriptAudit.ProetaleKummerCoefficientMap

open AlgebraicGeometry CategoryTheory Opposite
open ProetaleKummerRoots ProetaleKummerPower
open KummerRootLabels (mapRoots)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] {X : Scheme.{0}}
  (k : X ⟶ Spec (CommRingCat.of K)) (d : ℕ)

abbrev coefficientGroup (K : Type) [Field K] (d : ℕ) : G :=
  AddCommGrpCat.of (ULift.{1} (Additive (rootsOfUnity d K)))

def coefficientMap (U : X.ProEt) : CommRingCat.of K ⟶ coordinates X U :=
  (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (U.hom ≫ k).appTop

theorem coefficientMap_natural {U V : X.ProEt} (f : U ⟶ V) :
    coefficientMap k V ≫ f.left.appTop = coefficientMap k U := by
  rw [coefficientMap, Category.assoc, ← Scheme.Hom.comp_appTop, ← Category.assoc, f.w]
  rfl

/-- The canonical morphism from the constant presheaf of coefficient-field roots. -/
def constantToRoots : (Functor.const X.ProEtᵒᵖ).obj (coefficientGroup K d) ⟶ roots X d where
  app U := AddCommGrpCat.uliftFunctor.{1}.map ((ringRoots d).map (coefficientMap k U.unop))
  naturality {U V} f := by
    change _ ≫ _ =
      AddCommGrpCat.uliftFunctor.{1}.map ((ringRoots d).map (coefficientMap k U.unop)) ≫
      AddCommGrpCat.uliftFunctor.{1}.map ((ringRoots d).map f.unop.left.appTop)
    rw [Category.id_comp, ← Functor.map_comp, ← Functor.map_comp, coefficientMap_natural]

variable {R : CommRingCat.{0}} (g : Spec R ⟶ X) [WeaklyEtale g]

/-- The coefficient ring map in a displayed affine chart. -/
abbrev affineCoefficients : CommRingCat.of K ⟶ R := Spec.preimage (g ≫ k)

theorem affineCoefficients_formula :
    coefficientMap k (Scheme.ProEt.mk g) ≫ (Scheme.ΓSpecIso R).hom = affineCoefficients k g := by
  change (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (g ≫ k).appTop ≫ _ = _
  rw [Category.assoc, ← Spec.map_preimage (g ≫ k), Scheme.ΓSpecIso_naturality,
    Iso.inv_hom_id_assoc]

/-- On a displayed affine chart, regular-function roots identify with coordinate roots. -/
def specRoots :
    (roots X d).obj (op (Scheme.ProEt.mk g)) ≃+ Additive (rootsOfUnity d R) :=
  AddEquiv.ulift.trans (((ringRoots d).mapIso (Scheme.ΓSpecIso R)).addCommGroupIsoToAddEquiv)

theorem specRoots_coefficient (a : coefficientGroup K d) :
    specRoots d g ((constantToRoots k d).app (op (Scheme.ProEt.mk g)) a) =
      Additive.ofMul (mapRoots d (affineCoefficients k g).hom a.down.toMul) := by
  have h : (ringRoots d).map (coefficientMap k (Scheme.ProEt.mk g)) ≫
      ((ringRoots d).mapIso (Scheme.ΓSpecIso R)).hom =
        (ringRoots d).map (affineCoefficients k g) := by
    rw [Functor.mapIso_hom, ← Functor.map_comp, affineCoefficients_formula]
  exact ConcreteCategory.congr_hom h a.down

theorem specRoots_natural {T : CommRingCat.{0}} (r : R ⟶ T) [WeaklyEtale (Spec.map r ≫ g)]
    (s : (roots X d).obj (op (Scheme.ProEt.mk g))) :
    specRoots d (Spec.map r ≫ g)
        ((roots X d).map (MorphismProperty.Over.homMk (Spec.map r) rfl).op s) =
      Additive.ofMul (mapRoots d r.hom (specRoots d g s).toMul) := by
  have h : (ringRoots d).map (Spec.map r).appTop ≫
      ((ringRoots d).mapIso (Scheme.ΓSpecIso T)).hom =
      ((ringRoots d).mapIso (Scheme.ΓSpecIso R)).hom ≫ (ringRoots d).map r := by
    simp only [Functor.mapIso_hom, ← Functor.map_comp, Scheme.ΓSpecIso_naturality]
  exact ConcreteCategory.congr_hom h s.down

end
end ManuscriptAudit.ProetaleKummerCoefficientMap

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleKummerCoefficientMap.coefficientMap_natural,
      ``ManuscriptAudit.ProetaleKummerCoefficientMap.specRoots_coefficient,
      ``ManuscriptAudit.ProetaleKummerCoefficientMap.specRoots_natural] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
