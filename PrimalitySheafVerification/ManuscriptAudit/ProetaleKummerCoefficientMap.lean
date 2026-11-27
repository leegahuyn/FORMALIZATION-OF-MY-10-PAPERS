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
  rw [coefficientMap, Category.assoc, ← Scheme.Hom.comp_appTop, ← Category.assoc,
    MorphismProperty.Over.w f] <;> rfl

/-- The canonical morphism from the constant presheaf of coefficient-field roots. -/
def constantToRoots : (Functor.const X.ProEtᵒᵖ).obj (coefficientGroup K d) ⟶ roots X d where
  app U := AddCommGrpCat.uliftFunctor.{1}.map ((ringRoots d).map (coefficientMap k U.unop))
  naturality {U V} f := by
    change 𝟙 (coefficientGroup K d) ≫
        AddCommGrpCat.uliftFunctor.{1}.map ((ringRoots d).map (coefficientMap k V.unop)) =
      AddCommGrpCat.uliftFunctor.{1}.map ((ringRoots d).map (coefficientMap k U.unop)) ≫
      AddCommGrpCat.uliftFunctor.{1}.map ((ringRoots d).map f.unop.left.appTop)
    rw [Category.id_comp, ← Functor.map_comp, ← Functor.map_comp, coefficientMap_natural]

variable {R : CommRingCat.{0}} (g : Spec R ⟶ X) [WeaklyEtale g]

/-- The coefficient ring map in a displayed affine chart. -/
abbrev affineCoefficients : CommRingCat.of K ⟶ R := Spec.preimage (g ≫ k)

theorem affineCoefficients_formula :
    coefficientMap k (Scheme.ProEt.mk g) ≫ (Scheme.ΓSpecIso R).hom = affineCoefficients k g := by
  let f := affineCoefficients k g
  have hf : Spec.map f = g ≫ k := Spec.map_preimage _
  change (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (g ≫ k).appTop ≫ (Scheme.ΓSpecIso R).hom = f
  rw [← hf, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

/-- On a displayed affine chart, regular-function roots identify with coordinate roots. -/
def specRoots :
    (roots X d).obj (op (Scheme.ProEt.mk g)) ≃+ Additive (rootsOfUnity d R) :=
  AddEquiv.ulift.trans (((ringRoots d).mapIso (Scheme.ΓSpecIso R)).addCommGroupIsoToAddEquiv)

set_option maxHeartbeats 1000000 in
theorem specRoots_coefficient (a : coefficientGroup K d) :
    specRoots d g ((constantToRoots k d).app (op (Scheme.ProEt.mk g)) a) =
      Additive.ofMul (mapRoots d (affineCoefficients k g).hom a.down.toMul) := by
  let F := ringRoots d
  let x : F.obj (CommRingCat.of K) := a.down
  let f := coefficientMap k (Scheme.ProEt.mk g)
  let q := (Scheme.ΓSpecIso R).hom
  let r := affineCoefficients k g
  have h : F.map f ≫ F.map q = F.map r := by
    rw [← F.map_comp]
    exact congrArg F.map (affineCoefficients_formula k g)
  change (F.map q) ((F.map f) x) = (F.map r) x
  exact ConcreteCategory.congr_hom h x

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
