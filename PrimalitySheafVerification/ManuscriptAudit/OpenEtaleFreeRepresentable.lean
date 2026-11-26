import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
import Mathlib.CategoryTheory.Adjunction.Whiskering
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleExtension

/-!
# The free abelian sheaf of an open étale object

For an open immersion, evaluating an ambient sheaf at the open
represents the same functor as taking a section of its restriction.
Thus the free sheaf on the representable étale object is the constant
free abelian sheaf on the open extended by zero.
-/

namespace ManuscriptAudit.OpenEtaleExtension

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev C := AddCommGrpCat.{u}

/-- The free abelian sheaf on a representable object, as used in the native cohomology presheaf. -/
def freeEtaleRepresentable (X : Scheme.{u}) : X.Etale ⥤ Sheaf X.smallEtaleTopology C.{u} :=
  yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf X.smallEtaleTopology C.{u}

private abbrev integerGroup : C.{u} := AddCommGrpCat.of (ULift.{u} ℤ)

private abbrev freeSheafAdjunction (X : Scheme.{u}) :=
  (Adjunction.whiskerRight X.Etaleᵒᵖ AddCommGrpCat.adj).comp
    (sheafificationAdjunction X.smallEtaleTopology C.{u})

private def freeRepresentableSections {X : Scheme.{u}}
    (W : X.Etale) (F : Sheaf X.smallEtaleTopology C.{u}) :
    ((freeEtaleRepresentable X).obj W ⟶ F) ≃ F.obj.obj (op W) :=
  ((freeSheafAdjunction X).homEquiv (yoneda.obj W) F).trans yonedaEquiv

private theorem freeRepresentableSections_natural {X : Scheme.{u}}
    (W : X.Etale) {F G : Sheaf X.smallEtaleTopology C.{u}}
    (f : (freeEtaleRepresentable X).obj W ⟶ F) (g : F ⟶ G) :
    freeRepresentableSections W G (f ≫ g) =
      g.hom.app (op W) (freeRepresentableSections W F f) := by
  let a := freeSheafAdjunction X
  change yonedaEquiv ((a.homEquiv (yoneda.obj W) G) (f ≫ g)) =
    g.hom.app (op W) (yonedaEquiv ((a.homEquiv (yoneda.obj W) F) f))
  rw [a.homEquiv_naturality_right, yonedaEquiv_comp]
  rfl

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

private abbrev terminalObject := Scheme.Etale.mk (𝟙 U)
private abbrev openObject := (etalePostcompose j).obj (terminalObject (U := U))

private def openObjectIso :
    openObject j ≅ Scheme.Etale.mk j :=
  MorphismProperty.Over.isoMk (Iso.refl U) (by rfl)

private abbrev openIntegerSheaf :=
  (constantSheaf U.smallEtaleTopology C.{u}).obj integerGroup

private abbrev extensionSectionsAdjunction :=
  (constantSheafAdj U.smallEtaleTopology C.{u}
    (MorphismProperty.Over.mkIdTerminal @Etale U)).comp (abelianExtensionByZeroAdjunction j)

private def extensionSections (F : Sheaf X.smallEtaleTopology C.{u}) :
    ((extensionByZero j C.{u}).obj (openIntegerSheaf (U := U)) ⟶ F) ≃
      F.obj.obj (op (openObject j)) :=
  ((extensionSectionsAdjunction j).homEquiv integerGroup F).trans
    ((AddCommGrpCat.coyonedaObjIsoForget).app (F.obj.obj (op (openObject j)))).toEquiv

private theorem extensionSections_natural {F G : Sheaf X.smallEtaleTopology C.{u}}
    (f : (extensionByZero j C.{u}).obj (openIntegerSheaf (U := U)) ⟶ F) (g : F ⟶ G) :
    extensionSections j G (f ≫ g) =
      g.hom.app (op (openObject j)) (extensionSections j F f) := by
  let a := extensionSectionsAdjunction j
  let e := AddCommGrpCat.coyonedaObjIsoForget.{u}
  let W := openObject j
  let t := (a.homEquiv integerGroup F) f
  change e.hom.app (G.obj.obj (op W)) ((a.homEquiv integerGroup G) (f ≫ g)) =
    g.hom.app (op W) (e.hom.app (F.obj.obj (op W)) t)
  rw [a.homEquiv_naturality_right]
  exact congrArg (fun φ => φ t) (e.hom.naturality (g.hom.app (op W)))

/-- The free sheaf on the ordinary open object is the free constant sheaf extended by zero. -/
def freeEtaleRepresentableOpenIso :
    (freeEtaleRepresentable X).obj (Scheme.Etale.mk j) ≅
      (extensionByZero j C.{u}).obj (openIntegerSheaf (U := U)) := by
  let W := openObject j
  let A := (freeEtaleRepresentable X).obj W
  let B := (extensionByZero j C.{u}).obj (openIntegerSheaf (U := U))
  let e (F : Sheaf X.smallEtaleTopology C.{u}) :
      (A ⟶ F) ≃ (B ⟶ F) :=
    (freeRepresentableSections W F).trans (extensionSections j F).symm
  have h : A ≅ B := by
    apply Coyoneda.ext A B (fun {F} => e F) (fun {F} => (e F).symm)
    · intro F f
      exact (e F).symm_apply_apply f
    · intro F f
      exact (e F).apply_symm_apply f
    · intro F G g f
      apply (freeRepresentableSections W G).injective
      change (freeRepresentableSections W G) ((freeRepresentableSections W G).symm
          (extensionSections j G (f ≫ g))) =
        (freeRepresentableSections W G) ((freeRepresentableSections W F).symm
          (extensionSections j F f) ≫ g)
      rw [Equiv.apply_symm_apply, freeRepresentableSections_natural,
        Equiv.apply_symm_apply, extensionSections_natural]
  exact ((freeEtaleRepresentable X).mapIso (openObjectIso j)).symm ≪≫ h

end

end ManuscriptAudit.OpenEtaleExtension

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.OpenEtaleExtension.freeEtaleRepresentableOpenIso
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
