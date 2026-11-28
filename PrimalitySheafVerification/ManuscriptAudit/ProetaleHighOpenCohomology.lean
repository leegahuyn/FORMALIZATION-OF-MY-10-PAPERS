import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import PrimalitySheafVerification.ManuscriptAudit.ProetaleMayerVietorisRepresentable

/-! Sheaf cohomology at an open object on the universe-lifted native site
is the actual ordinary native cohomology of the open. -/

namespace ManuscriptAudit.ProetaleHighOpenCohomology

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open ProetaleMayerVietorisSite (siteEquivalence topology sheafEquivalence)
open ProetaleMayerVietorisRepresentable (nativeFree openIso terminalIso)
open ProetaleOpenLocalLifts (openObject identityObject)
open ProetaleOpenExtAdjunction (integers openExtEquiv)
open OpenProetaleExtension (restriction extensionByZero)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{1}
private abbrev C (X : Scheme.{0}) := Sheaf (Scheme.ProEt.topology X) A
private abbrev D (X : Scheme.{0}) := Sheaf (topology X) A

variable {X : Scheme.{0}}

abbrev coefficient (F : C X) := (sheafEquivalence X).functor.obj F

abbrev liftedObject (W : X.ProEt) := (siteEquivalence X).functor.obj W

private abbrev highFree (W : X.ProEt) :=
  (presheafToSheaf (topology X) A).obj (yoneda.obj (liftedObject W) ⋙ AddCommGrpCat.free)

set_option maxHeartbeats 4500000 in
/-- The native and universe-lifted free representables compute the same Ext. -/
def freeEquiv (F : C X) (W : X.ProEt) (n : ℕ) :
    (coefficient F).H' n (liftedObject W) ≃+ Ext (nativeFree W) F n := by
  let e := sheafEquivalence X
  let E := e.inverse
  letI : EnoughInjectives (D X) := IsGrothendieckAbelian.enoughInjectives.{1} (C := D X)
  letI : E.Additive := E.additive_of_preserves_binary_products
  let T := e.functor.obj F
  let P := highFree W
  let q := AddEquiv.ofBijective (E.mapExtAddHom P T n)
    (E.mapExt_bijective_of_preservesInjectiveObjects P T n)
  let i : E.obj T ≅ F := e.unitIso.symm.app F
  let t := ((extFunctor (C := C X) n).obj (op (nativeFree W))).mapIso i
  exact q.trans t.addCommGroupIsoToAddEquiv

/-- The lifted native open-object groups agree with the ordinary groups on the open. -/
def openEquiv {U : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : C X) (n : ℕ) :
    (coefficient F).H' n (liftedObject (openObject j)) ≃+
      Sheaf.H ((restriction j A).obj F) n :=
  (freeEquiv F (openObject j) n).trans
    ((((extFunctor (C := C X) n).mapIso (openIso j).symm.op).app F).addCommGroupIsoToAddEquiv.trans
      (openExtEquiv j F n))

/-- The lifted native terminal-object groups agree with ambient native cohomology. -/
def terminalEquiv (F : C X) (n : ℕ) :
    (coefficient F).H' n (liftedObject (identityObject X)) ≃+ Sheaf.H F n :=
  (freeEquiv F (identityObject X) n).trans
    (((extFunctor (C := C X) n).mapIso (terminalIso X).symm.op).app F).addCommGroupIsoToAddEquiv

end
end ManuscriptAudit.ProetaleHighOpenCohomology

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleHighOpenCohomology.freeEquiv,
      ``ManuscriptAudit.ProetaleHighOpenCohomology.openEquiv,
      ``ManuscriptAudit.ProetaleHighOpenCohomology.terminalEquiv] do
    let ax ← collectAxioms name
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
