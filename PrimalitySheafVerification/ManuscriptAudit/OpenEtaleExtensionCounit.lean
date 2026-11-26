import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleExtensionComposition
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleExtensionMono

/-!
# Counit of étale extension by zero

At an interior geometric point the unit of extension and restriction is
an isomorphism on stalks. The triangle identity then identifies the
counit as an isomorphism at such a point. At an exterior point its source
is zero, so the actual counit is a monomorphism.
-/

namespace ManuscriptAudit.OpenEtaleExtension

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

private abbrev C := AddCommGrpCat.{u}

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private theorem extensionUnit_hom (F : Sheaf U.smallEtaleTopology C.{u}) :
    letI := hasLeftKanExtension j C.{u}
    let G := (etalePostcompose j).op
    ((abelianExtensionByZeroAdjunction j).unit.app F).hom =
      G.lanUnit.app F.obj ≫
        Functor.whiskerLeft G (toSheafify X.smallEtaleTopology (G.lan.obj F.obj)) := by
  let G := (etalePostcompose j).op
  letI := postcomposeContinuous j
  letI := hasLeftKanExtension j C.{u}
  let a := (G.lanAdjunction C.{u}).comp (sheafificationAdjunction X.smallEtaleTopology C.{u})
  let b : extensionByZero j C.{u} ⊣ restriction j C.{u} :=
    a.restrictFullyFaithful (fullyFaithfulSheafToPresheaf U.smallEtaleTopology C.{u})
      (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)
  change (sheafToPresheaf U.smallEtaleTopology C.{u}).map (b.unit.app F) = _
  dsimp only [b]
  rw [Adjunction.map_restrictFullyFaithful_unit_app]
  simp only [Iso.refl_hom, NatTrans.id_app, Functor.map_id, Category.id_comp, Category.comp_id]
  change ((G.lanAdjunction C.{u}).comp (sheafificationAdjunction X.smallEtaleTopology C.{u})).unit.app
    F.obj = _
  rw [Adjunction.comp_unit_app, Functor.lanAdjunction_unit] <;> rfl

/-- The unit of extension by zero is an isomorphism at each geometric stalk of the open. -/
theorem extensionUnit_stalk_isIso {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ U) (F : Sheaf U.smallEtaleTopology C.{u}) :
    IsIso ((Scheme.pointSmallEtale s).sheafFiber.map
      ((abelianExtensionByZeroAdjunction j).unit.app F)) := by
  let G := (etalePostcompose j).op
  letI := (postcomposeFullyFaithful j).full
  letI := (postcomposeFullyFaithful j).faithful
  letI := hasLeftKanExtension j C.{u}
  letI := hasPointwiseLeftKanExtension j C.{u} F.obj
  let Φ := Scheme.pointSmallEtale s
  let Ψ := Scheme.pointSmallEtale (s ≫ j)
  let t := toSheafify X.smallEtaleTopology (G.lan.obj F.obj)
  have h : IsIso ((Ψ.presheafFiber (A := C.{u})).map t) := inferInstance
  letI : IsIso ((Φ.presheafFiber (A := C.{u})).map (Functor.whiskerLeft G t)) :=
    (NatIso.isIso_map_iff (presheafFiberComparisonNatIso j s) t).mp h
  change IsIso ((Φ.presheafFiber (A := C.{u})).map ((abelianExtensionByZeroAdjunction j).unit.app F).hom)
  rw [extensionUnit_hom, Functor.map_comp]
  infer_instance

/-- The counit is an isomorphism at a geometric point that factors through the open. -/
theorem extensionCounit_stalk_isIso {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ U) (F : Sheaf X.smallEtaleTopology C.{u}) :
    IsIso ((Scheme.pointSmallEtale (s ≫ j)).sheafFiber.map
      ((abelianExtensionByZeroAdjunction j).counit.app F)) := by
  let a := abelianExtensionByZeroAdjunction j
  let Φ := Scheme.pointSmallEtale s
  let R := restriction j C.{u}
  let e := restrictionStalkNatIso j s
  apply (NatIso.isIso_map_iff e (a.counit.app F)).mp
  change IsIso ((Φ.sheafFiber (A := C.{u})).map (R.map (a.counit.app F)))
  let η := (Φ.sheafFiber (A := C.{u})).map (a.unit.app (R.obj F))
  let ε := (Φ.sheafFiber (A := C.{u})).map (R.map (a.counit.app F))
  have h : η ≫ ε = 𝟙 _ := by
    calc
      η ≫ ε = (Φ.sheafFiber (A := C.{u})).map
          (a.unit.app (R.obj F) ≫ R.map (a.counit.app F)) :=
        ((Φ.sheafFiber (A := C.{u})).map_comp _ _).symm
      _ = (Φ.sheafFiber (A := C.{u})).map (𝟙 (R.obj F)) :=
        congrArg (fun f : R.obj F ⟶ R.obj F => (Φ.sheafFiber (A := C.{u})).map f)
          (a.right_triangle_components F)
      _ = 𝟙 _ := (Φ.sheafFiber (A := C.{u})).map_id _
  letI : IsIso η := extensionUnit_stalk_isIso j s (R.obj F)
  letI : IsIso (η ≫ ε) := by rw [h]; infer_instance
  exact IsIso.of_isIso_comp_left η ε

/-- The actual counit is a monomorphism into the ambient sheaf. -/
theorem extensionCounit_mono (F : Sheaf X.smallEtaleTopology C.{u}) :
    Mono ((abelianExtensionByZeroAdjunction j).counit.app F) := by
  apply mono_of_geometric_stalks
  intro Ω _ _ s
  by_cases hs : ∃ t : Spec (.of Ω) ⟶ U, t ≫ j = s
  · obtain ⟨t, rfl⟩ := hs
    letI := extensionCounit_stalk_isIso j t F
    infer_instance
  · exact (extensionByZero_stalk_isZero j s hs ((restriction j C.{u}).obj F)).mono _

/-- The native nested-open map of the extended constant sheaves is a monomorphism. -/
theorem nestedOpenConstantMap_mono {V : Scheme.{u}} (i : V ⟶ U) [IsOpenImmersion i] (M : C.{u}) :
    Mono (nestedOpenConstantMap i j M) := by
  let a := abelianExtensionByZeroAdjunction i
  let F := (constantSheaf U.smallEtaleTopology C.{u}).obj M
  let e := (restrictionConstantIso i).inv.app M
  have h : ((a.homEquiv _ F).symm e) =
      (extensionByZero i C.{u}).map e ≫ a.counit.app F := by
    rw [Adjunction.homEquiv_counit]
  letI : Mono (a.counit.app F) := extensionCounit_mono i F
  haveI : Mono ((a.homEquiv _ F).symm e) := by rw [h]; infer_instance
  letI := extensionByZero_map_mono j ((a.homEquiv _ F).symm e)
  unfold nestedOpenConstantMap
  infer_instance

end

end ManuscriptAudit.OpenEtaleExtension

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.OpenEtaleExtension.extensionUnit_stalk_isIso,
      ``ManuscriptAudit.OpenEtaleExtension.extensionCounit_stalk_isIso,
      ``ManuscriptAudit.OpenEtaleExtension.extensionCounit_mono,
      ``ManuscriptAudit.OpenEtaleExtension.nestedOpenConstantMap_mono] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
