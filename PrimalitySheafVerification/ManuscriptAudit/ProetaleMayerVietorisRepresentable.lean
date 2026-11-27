import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
import Mathlib.CategoryTheory.Adjunction.Whiskering
import PrimalitySheafVerification.ManuscriptAudit.ProetaleMayerVietorisSite
import PrimalitySheafVerification.ManuscriptAudit.ProetaleOpenExtAdjunction

/-! The free abelian sheaves in the native cover complex are the integer
sheaf at the terminal object and its actual extensions by zero on opens. -/

namespace ManuscriptAudit.ProetaleMayerVietorisRepresentable

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleMayerVietorisSite (siteEquivalence sheafEquivalence topology)
open ProetaleOpenExtAdjunction (integers)
open OpenProetaleExtension (abelianExtensionByZeroAdjunction extensionByZero)
open ProetaleOpenLocalLifts (identityObject openObject)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{1}
private abbrev S (X : Scheme.{0}) := Sheaf (Scheme.ProEt.topology X) A
private abbrev Z := AddCommGrpCat.of (ULift.{1} ℤ)

private abbrev liftedObject {X : Scheme.{0}} (W : X.ProEt) :=
  (siteEquivalence X).functor.obj W

private abbrev highFree {X : Scheme.{0}} (W : X.ProEt) :=
  (presheafToSheaf (topology X) A).obj (yoneda.obj (liftedObject W) ⋙ AddCommGrpCat.free)

/-- The actual native free representable from the higher-universe site. -/
abbrev nativeFree {X : Scheme.{0}} (W : X.ProEt) : S X :=
  (sheafEquivalence X).inverse.obj (highFree W)

private abbrev freeAdj (X : Scheme.{0}) :=
  (Adjunction.whiskerRight (AsSmall.{1} X.ProEt)ᵒᵖ AddCommGrpCat.adj).comp
    (sheafificationAdjunction (topology X) A)

private def freeSections {X : Scheme.{0}} (W : X.ProEt) (F : S X) :
    (nativeFree W ⟶ F) ≃ F.obj.obj (op W) :=
  ((sheafEquivalence X).symm.toAdjunction.homEquiv (highFree W) F).trans
    (((freeAdj X).homEquiv (yoneda.obj (liftedObject W)) ((sheafEquivalence X).functor.obj F)).trans
      yonedaEquiv)

private theorem freeSections_natural {X : Scheme.{0}} (W : X.ProEt) {F G : S X}
    (f : nativeFree W ⟶ F) (g : F ⟶ G) :
    freeSections W G (f ≫ g) = g.hom.app (op W) (freeSections W F f) := by
  let e := sheafEquivalence X
  let a := e.symm.toAdjunction
  let b := freeAdj X
  let T := yoneda.obj (liftedObject W)
  change yonedaEquiv ((b.homEquiv T (e.functor.obj G)) ((a.homEquiv (highFree W) G) (f ≫ g))) =
    g.hom.app (op W)
      (yonedaEquiv ((b.homEquiv T (e.functor.obj F)) ((a.homEquiv (highFree W) F) f)))
  rw [a.homEquiv_naturality_right, b.homEquiv_naturality_right, yonedaEquiv_comp]
  rfl

private abbrev eval {X : Scheme.{0}} (W : X.ProEt) :=
  (sheafSections (Scheme.ProEt.topology X) A).obj (op W)

private def integerSections {X : Scheme.{0}} (W : X.ProEt) {G : A ⥤ S X}
    (a : G ⊣ eval W) (F : S X) : (G.obj Z ⟶ F) ≃ F.obj.obj (op W) :=
  (a.homEquiv Z F).trans
    (AddCommGrpCat.coyonedaObjIsoForget.{1}.app (F.obj.obj (op W))).toEquiv

private theorem integerSections_natural {X : Scheme.{0}} (W : X.ProEt) {E : A ⥤ S X}
    (a : E ⊣ eval W) {F G : S X} (f : E.obj Z ⟶ F) (g : F ⟶ G) :
    integerSections W a G (f ≫ g) = g.hom.app (op W) (integerSections W a F f) := by
  let e := AddCommGrpCat.coyonedaObjIsoForget.{1}
  let t := (a.homEquiv Z F) f
  change e.hom.app (G.obj.obj (op W)) ((a.homEquiv Z G) (f ≫ g)) =
    g.hom.app (op W) (e.hom.app (F.obj.obj (op W)) t)
  rw [a.homEquiv_naturality_right]
  exact congrArg (fun φ ↦ φ t) (e.hom.naturality (g.hom.app (op W)))

private def freeIsoOfAdjunction {X : Scheme.{0}} (W : X.ProEt) {E : A ⥤ S X}
    (a : E ⊣ eval W) : nativeFree W ≅ E.obj Z := by
  let e (F : S X) : (nativeFree W ⟶ F) ≃ (E.obj Z ⟶ F) :=
    (freeSections W F).trans (integerSections W a F).symm
  apply Coyoneda.ext (nativeFree W) (E.obj Z) (fun {F} ↦ e F) (fun {F} ↦ (e F).symm)
  · intro F f
    exact (e F).symm_apply_apply f
  · intro F f
    exact (e F).apply_symm_apply f
  · intro F G f g
    apply (freeSections W G).injective
    change freeSections W G ((freeSections W G).symm (integerSections W a G (f ≫ g))) =
      freeSections W G ((freeSections W F).symm (integerSections W a F f) ≫ g)
    rw [Equiv.apply_symm_apply, freeSections_natural, Equiv.apply_symm_apply,
      integerSections_natural]

/-- The terminal free representable is the actual native integer coefficient sheaf. -/
def terminalIso (X : Scheme.{0}) : nativeFree (identityObject X) ≅ integers X :=
  freeIsoOfAdjunction (identityObject X)
    (constantSheafAdj (Scheme.ProEt.topology X) A (MorphismProperty.Over.mkIdTerminal @WeaklyEtale X))

/-- At an open chart this free representable is the actual extension by zero of the integer sheaf. -/
def openIso {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j] :
    nativeFree (openObject j) ≅ (extensionByZero j A).obj (integers U) :=
  freeIsoOfAdjunction (openObject j)
    ((constantSheafAdj (Scheme.ProEt.topology U) A
      (MorphismProperty.Over.mkIdTerminal @WeaklyEtale U)).comp
      (abelianExtensionByZeroAdjunction j))

end
end ManuscriptAudit.ProetaleMayerVietorisRepresentable

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleMayerVietorisRepresentable.terminalIso,
      ``ManuscriptAudit.ProetaleMayerVietorisRepresentable.openIso] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
