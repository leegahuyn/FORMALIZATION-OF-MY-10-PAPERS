import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import PrimalitySheafVerification.ManuscriptAudit.EtaleContinuousMapSheaf
import PrimalitySheafVerification.ManuscriptAudit.GeometricSkyscraperHZero
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleExtensionCounit

/-!
# Degree-zero cohomology of a proper open extension

On a preconnected ambient scheme a section of the constant sheaf is
determined by its germ at one geometric point. A section of an extension
by zero has zero germ at a point outside the open.
-/

namespace ManuscriptAudit.OpenEtaleExtension

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open EtaleContinuousMapSheaf GeometricSkyscraperCohomology

noncomputable section

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] etaleSiteHasExt

private abbrev identityEtale (X : Scheme.{u}) : X.Etale := Scheme.Etale.mk (𝟙 X)

private def identityEtalePoint {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (CommRingCat.of Ω) ⟶ X) :
    (Scheme.pointSmallEtale s).fiber.obj (identityEtale X) :=
  Over.homMk s (Category.comp_id _)

/-- A global continuous map into a discrete group is determined by its étale germ
at a geometric point of a preconnected scheme. -/
theorem continuousMapGlobalGerm_injective {X : Scheme.{u}} [PreconnectedSpace X]
    (M : AddCommGrpCat.{u}) [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalAddGroup M]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (CommRingCat.of Ω) ⟶ X) :
    Function.Injective ((Scheme.pointSmallEtale s).toPresheafFiber
      (identityEtale X) (identityEtalePoint s) (continuousMapSheaf X M).obj) := by
  let W := identityEtale X
  let Φ := Scheme.pointSmallEtale s
  let t := identityEtalePoint s
  let P := (continuousMapSheaf X M).obj
  intro a b h
  obtain ⟨V, f, v, _, hv⟩ := (Φ.toPresheafFiber_eq_iff' (P := P) W t a b).mp h
  let v₀ : V.left := v.left (default : Spec (CommRingCat.of Ω))
  have h₀ : a (f.left v₀) = b (f.left v₀) :=
    congrArg (fun g : C(V.left, M) => g v₀) hv
  apply ContinuousMap.ext
  intro x
  exact (TotallyDisconnectedSpace.eq_of_continuous a a.continuous x (f.left v₀)).trans
    (h₀.trans (TotallyDisconnectedSpace.eq_of_continuous b b.continuous (f.left v₀) x))

/-- If a geometric point lies outside an open in a preconnected ambient scheme,
degree-zero étale cohomology of the constant abelian sheaf extended by zero vanishes. -/
theorem extensionByZeroConstantHZero_subsingleton {U X : Scheme.{u}} [PreconnectedSpace X]
    (j : U ⟶ X) [IsOpenImmersion j] (M : AddCommGrpCat.{u})
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (CommRingCat.of Ω) ⟶ X)
    (hs : ¬ ∃ t : Spec (CommRingCat.of Ω) ⟶ U, t ≫ j = s) :
    Subsingleton (Sheaf.H ((extensionByZero j AddCommGrpCat.{u}).obj
      ((constantSheaf U.smallEtaleTopology AddCommGrpCat.{u}).obj M)) 0) := by
  letI : TopologicalSpace M := ⊥
  letI : DiscreteTopology M := ⟨rfl⟩
  let E := (extensionByZero j AddCommGrpCat.{u}).obj
    ((constantSheaf U.smallEtaleTopology AddCommGrpCat.{u}).obj M)
  let G := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj M
  let F := continuousMapSheaf X M
  let e := (extensionByZero j AddCommGrpCat.{u}).mapIso ((restrictionConstantIso j).app M).symm
  let a := (abelianExtensionByZeroAdjunction j).counit.app G
  let m : E ⟶ F := e.hom ≫ a ≫ (constantSheafContinuousMapIso X M).hom
  letI : Mono a := extensionCounit_mono j G
  letI : Mono m := by dsimp only [m]; infer_instance
  let W := identityEtale X
  let Φ := Scheme.pointSmallEtale s
  let t := identityEtalePoint s
  let hW : IsTerminal W := MorphismProperty.Over.mkIdTerminal @Etale X
  let T := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  have hinj : Function.Injective (Sheaf.H.map m 0) :=
    Ext.postcomp_mk₀_injective_of_mono T m
  have hgerm := continuousMapGlobalGerm_injective M s
  letI : Subsingleton (Φ.sheafFiber.obj E) :=
    AddCommGrpCat.subsingleton_of_isZero
      (extensionByZero_stalk_isZero j s hs ((constantSheaf U.smallEtaleTopology AddCommGrpCat.{u}).obj M))
  have hzero (x : Sheaf.H E 0) : x = 0 := by
    apply hinj
    apply (Sheaf.H.equiv₀ F hW).injective
    apply hgerm
    have hx : Φ.toPresheafFiber W t E.obj (Sheaf.H.equiv₀ E hW x) = 0 :=
      Subsingleton.elim _ _
    calc
      Φ.toPresheafFiber W t F.obj (Sheaf.H.equiv₀ F hW (Sheaf.H.map m 0 x)) =
          Φ.sheafFiber.map m (Φ.toPresheafFiber W t E.obj (Sheaf.H.equiv₀ E hW x)) := by
        rw [← Sheaf.H.equiv₀_naturality]
        exact (Φ.toPresheafFiber_naturality_apply m.hom W t _).symm
      _ = 0 := by rw [hx, map_zero]
      _ = Φ.toPresheafFiber W t F.obj (Sheaf.H.equiv₀ F hW (Sheaf.H.map m 0 0)) := by
        simp only [map_zero]
  exact ⟨fun x y => (hzero x).trans (hzero y).symm⟩

end

end ManuscriptAudit.OpenEtaleExtension

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.OpenEtaleExtension.continuousMapGlobalGerm_injective,
      ``ManuscriptAudit.OpenEtaleExtension.extensionByZeroConstantHZero_subsingleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
