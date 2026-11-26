import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Sites.Point.Conservative
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleExtensionInsideStalk
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleExtensionStalk

/-!
# Monomorphisms under étale extension by zero

The genuine extension by zero preserves monomorphisms. Its map on a
geometric stalk is either the original stalk map in the open or a map
between zero objects outside the open.
-/

namespace ManuscriptAudit.OpenEtaleExtension

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev C := AddCommGrpCat.{u}

/-- Geometric stalks on the small étale site jointly detect monomorphisms. -/
theorem mono_of_geometric_stalks {X : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology C} (f : F ⟶ G)
    (h : ∀ {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
      Mono ((Scheme.pointSmallEtale s).sheafFiber.map f)) : Mono f := by
  let geometricPoint (x : X) : Spec (.of (SeparableClosure (X.residueField x))) ⟶ X :=
    (Scheme.SpecToEquivOfField (SeparableClosure (X.residueField x)) X).2
      ⟨x, CommRingCat.ofHom (algebraMap (X.residueField x) _)⟩
  let P := ObjectProperty.ofObj (fun x : X => Scheme.pointSmallEtale (geometricPoint x))
  have hP : P.IsConservativeFamilyOfPoints :=
    Scheme.isConservativeFamilyOfPoints_pointSmallEtale' X
  letI : ∀ p : P.FullSubcategory, Mono (p.obj.sheafFiber.map f) := fun p => by
    obtain ⟨x, hx⟩ := (ObjectProperty.ofObj_iff p.obj).mp p.property
    rw [← hx]
    exact h (geometricPoint x)
  exact (hP.jointlyReflectMonomorphisms C).mono f

/-- The actual extension by zero takes monomorphisms of sheaves to monomorphisms. -/
theorem extensionByZero_map_mono {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {F G : Sheaf U.smallEtaleTopology C} (f : F ⟶ G) [Mono f] :
    Mono ((extensionByZero j C).map f) := by
  apply mono_of_geometric_stalks
  intro Ω _ _ s
  by_cases hs : ∃ t : Spec (.of Ω) ⟶ U, t ≫ j = s
  · obtain ⟨t, rfl⟩ := hs
    let e := extensionByZeroStalkNatIso j t
    let m := (Scheme.pointSmallEtale (t ≫ j)).sheafFiber.map ((extensionByZero j C).map f)
    let n := (Scheme.pointSmallEtale t).sheafFiber.map f
    letI : Mono n := inferInstance
    have hn : m ≫ e.hom.app G = e.hom.app F ≫ n := e.hom.naturality f
    refine ⟨fun {Z} a b hab => ?_⟩
    apply (cancel_mono (e.hom.app F)).mp
    apply (cancel_mono n).mp
    simpa only [Category.assoc, ← hn] using congrArg (fun c => c ≫ e.hom.app G) hab
  · exact (extensionByZero_stalk_isZero j s hs F).mono _

end

end ManuscriptAudit.OpenEtaleExtension

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.OpenEtaleExtension.mono_of_geometric_stalks,
      ``ManuscriptAudit.OpenEtaleExtension.extensionByZero_map_mono] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
