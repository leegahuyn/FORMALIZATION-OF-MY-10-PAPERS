import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleExtensionCounit

/-! The actual extension by zero of a constant is unchanged by an isomorphism of its open source. -/

namespace ManuscriptAudit.OpenEtaleExtension

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev C := AddCommGrpCat.{u}

private theorem isIso_of_geometric_stalks {X : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology C.{u}} (f : F ⟶ G)
    (h : ∀ {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
      IsIso ((Scheme.pointSmallEtale s).sheafFiber.map f)) : IsIso f := by
  let geometricPoint (x : X) : Spec (.of (SeparableClosure (X.residueField x))) ⟶ X :=
    (Scheme.SpecToEquivOfField (SeparableClosure (X.residueField x)) X).2
      ⟨x, CommRingCat.ofHom (algebraMap (X.residueField x) _)⟩
  let P := ObjectProperty.ofObj (fun x : X ↦ Scheme.pointSmallEtale (geometricPoint x))
  have hP : P.IsConservativeFamilyOfPoints :=
    Scheme.isConservativeFamilyOfPoints_pointSmallEtale' X
  apply ((hP.jointlyReflectIsomorphisms C.{u}).isIso_iff f).mpr
  intro p
  obtain ⟨x, hx⟩ := (ObjectProperty.ofObj_iff
    (fun x : X ↦ Scheme.pointSmallEtale (geometricPoint x)) p.obj).mp p.property
  rw [← hx]
  exact h (geometricPoint x)

variable {V U X : Scheme.{u}} (i : V ⟶ U) [IsIso i]

private theorem counit_isIso_of_iso (F : Sheaf U.smallEtaleTopology C.{u}) :
    IsIso ((abelianExtensionByZeroAdjunction i).counit.app F) := by
  apply isIso_of_geometric_stalks
  intro Ω _ _ s
  have h : (s ≫ inv i) ≫ i = s := by simp
  let P (t : Spec (CommRingCat.of Ω) ⟶ U) : Prop :=
    IsIso ((Scheme.pointSmallEtale t).sheafFiber.map
      ((abelianExtensionByZeroAdjunction i).counit.app F))
  have hs : P ((s ≫ inv i) ≫ i) := extensionCounit_stalk_isIso i (s ≫ inv i) F
  exact Eq.mp (congrArg P h) hs

/-- Along a scheme isomorphism, extending the constant abelian sheaf returns the constant sheaf. -/
def extensionByZeroConstantIsoOfIso (M : C.{u}) :
    (extensionByZero i C.{u}).obj ((constantSheaf V.smallEtaleTopology C.{u}).obj M) ≅
      (constantSheaf U.smallEtaleTopology C.{u}).obj M := by
  let F := (constantSheaf U.smallEtaleTopology C.{u}).obj M
  letI := counit_isIso_of_iso i F
  exact (extensionByZero i C.{u}).mapIso ((restrictionConstantIso i).app M).symm ≪≫
    asIso ((abelianExtensionByZeroAdjunction i).counit.app F)

/-- The actual open extension of a constant agrees after an isomorphism of source schemes. -/
def extensionByZeroConstantIsoDomain (j : U ⟶ X) [IsOpenImmersion j] (M : C.{u}) :
    (extensionByZero (i ≫ j) C.{u}).obj ((constantSheaf V.smallEtaleTopology C.{u}).obj M) ≅
      (extensionByZero j C.{u}).obj ((constantSheaf U.smallEtaleTopology C.{u}).obj M) :=
  (extensionByZeroCompIso i j).symm.app _ ≪≫
    (extensionByZero j C.{u}).mapIso (extensionByZeroConstantIsoOfIso i M)

end
end ManuscriptAudit.OpenEtaleExtension

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.OpenEtaleExtension.extensionByZeroConstantIsoOfIso,
      ``ManuscriptAudit.OpenEtaleExtension.extensionByZeroConstantIsoDomain] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
