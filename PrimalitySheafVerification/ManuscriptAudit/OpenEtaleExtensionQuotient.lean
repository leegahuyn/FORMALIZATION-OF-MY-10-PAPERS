import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleExtensionCounit

/-!
# Quotient of the extended constants for nested opens

The actual nested-open map has a short exact cokernel sequence. Stalks
of that cokernel vanish in the smaller open and outside the larger open,
and agree with the larger open's constant stalk between them.
-/

namespace ManuscriptAudit.OpenEtaleExtension

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

private abbrev C := AddCommGrpCat.{u}

variable {V U X : Scheme.{u}} (i : V ⟶ U) (j : U ⟶ X)
variable [IsOpenImmersion i] [IsOpenImmersion j] (M : C.{u})

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The short complex of the native nested-open map and its cokernel projection. -/
def nestedOpenQuotientSequence : ShortComplex (Sheaf X.smallEtaleTopology C.{u}) :=
  ShortComplex.cokernelSequence (nestedOpenConstantMap i j M)

private theorem cokernelSequence_shortExact_of_mono {D : Type*} [Category* D] [Abelian D]
    {A B : D} (f : A ⟶ B) (hf : Mono f) : (ShortComplex.cokernelSequence f).ShortExact := by
  letI : Mono f := hf
  exact ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact f)
    (inferInstanceAs (Mono f)) (inferInstanceAs (Epi (cokernel.π f)))

set_option backward.isDefEq.respectTransparency true in
theorem nestedOpenQuotientSequence_shortExact : (nestedOpenQuotientSequence i j M).ShortExact :=
  cokernelSequence_shortExact_of_mono (nestedOpenConstantMap i j M)
    (nestedOpenConstantMap_mono i j M)

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]

theorem nestedOpenConstantMap_stalk_isIso (s : Spec (.of Ω) ⟶ V) :
    IsIso ((Scheme.pointSmallEtale ((s ≫ i) ≫ j)).sheafFiber.map
      (nestedOpenConstantMap i j M)) := by
  let a := abelianExtensionByZeroAdjunction i
  let F := (constantSheaf U.smallEtaleTopology C.{u}).obj M
  let e := (restrictionConstantIso i).inv.app M
  let m := (a.homEquiv _ F).symm e
  let Φ := Scheme.pointSmallEtale (s ≫ i)
  let Ψ := Scheme.pointSmallEtale ((s ≫ i) ≫ j)
  have h : m = (extensionByZero i C.{u}).map e ≫ a.counit.app F :=
    a.homEquiv_counit _ F e
  letI : IsIso ((Φ.sheafFiber (A := C.{u})).map m) := by
    rw [h, Functor.map_comp]
    letI := extensionCounit_stalk_isIso i s F
    infer_instance
  letI : IsIso ((Ψ.sheafFiber (A := C.{u})).map ((extensionByZero j C.{u}).map m)) :=
    (NatIso.isIso_map_iff (extensionByZeroStalkNatIso j (s ≫ i)) m).mpr inferInstance
  unfold nestedOpenConstantMap
  rw [Functor.map_comp]
  infer_instance

/-- The quotient of the extended constants has zero stalk in the smaller open. -/
theorem nestedOpenQuotient_stalk_isZero_inside (s : Spec (.of Ω) ⟶ V) :
    IsZero ((Scheme.pointSmallEtale ((s ≫ i) ≫ j)).sheafFiber.obj
      (cokernel (nestedOpenConstantMap i j M))) := by
  let Φ := Scheme.pointSmallEtale ((s ≫ i) ≫ j)
  let f := nestedOpenConstantMap i j M
  letI : IsIso ((Φ.sheafFiber (A := C.{u})).map f) := nestedOpenConstantMap_stalk_isIso i j M s
  exact (isZero_cokernel_of_epi ((Φ.sheafFiber (A := C.{u})).map f)).of_iso
    (PreservesCokernel.iso Φ.sheafFiber f)

/-- At a geometric point of the larger open that does not lie in the smaller one,
the stalk of the quotient is the constant sheaf stalk of the larger open. -/
def nestedOpenQuotientStalkIso (s : Spec (.of Ω) ⟶ U)
    (hs : ¬ ∃ t : Spec (.of Ω) ⟶ V, t ≫ i = s) :
    (Scheme.pointSmallEtale (s ≫ j)).sheafFiber.obj (cokernel (nestedOpenConstantMap i j M)) ≅
      (Scheme.pointSmallEtale s).sheafFiber.obj ((constantSheaf U.smallEtaleTopology C.{u}).obj M) := by
  let Φ := Scheme.pointSmallEtale (s ≫ j)
  let f := nestedOpenConstantMap i j M
  have hs' : ¬ ∃ t : Spec (.of Ω) ⟶ V, t ≫ (i ≫ j) = s ≫ j := by
    rintro ⟨t, ht⟩
    exact hs ⟨t, (cancel_mono j).mp (by simpa only [Category.assoc] using ht)⟩
  have hz := extensionByZero_stalk_isZero (i ≫ j) (s ≫ j) hs'
    ((constantSheaf V.smallEtaleTopology C.{u}).obj M)
  have hf : (Φ.sheafFiber (A := C.{u})).map f = 0 := hz.eq_of_src _ _
  exact PreservesCokernel.iso Φ.sheafFiber f ≪≫ cokernelIsoOfEq hf ≪≫ cokernelZeroIsoTarget ≪≫
    extensionByZeroStalkIso j s ((constantSheaf U.smallEtaleTopology C.{u}).obj M)

/-- The quotient of the extended constants has zero stalk outside the larger open. -/
theorem nestedOpenQuotient_stalk_isZero_outside (s : Spec (.of Ω) ⟶ X)
    (hs : ¬ ∃ t : Spec (.of Ω) ⟶ U, t ≫ j = s) :
    IsZero ((Scheme.pointSmallEtale s).sheafFiber.obj (cokernel (nestedOpenConstantMap i j M))) := by
  let Φ := Scheme.pointSmallEtale s
  let f := nestedOpenConstantMap i j M
  have hs' : ¬ ∃ t : Spec (.of Ω) ⟶ V, t ≫ (i ≫ j) = s := by
    rintro ⟨t, ht⟩
    exact hs ⟨t ≫ i, by simpa only [Category.assoc] using ht⟩
  have hz := extensionByZero_stalk_isZero (i ≫ j) s hs'
    ((constantSheaf V.smallEtaleTopology C.{u}).obj M)
  have hf : (Φ.sheafFiber (A := C.{u})).map f = 0 := hz.eq_of_src _ _
  exact (extensionByZero_stalk_isZero j s hs ((constantSheaf U.smallEtaleTopology C.{u}).obj M)).of_iso
    (PreservesCokernel.iso Φ.sheafFiber f ≪≫ cokernelIsoOfEq hf ≪≫ cokernelZeroIsoTarget)

end

end ManuscriptAudit.OpenEtaleExtension

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.OpenEtaleExtension.nestedOpenQuotientSequence_shortExact,
      ``ManuscriptAudit.OpenEtaleExtension.nestedOpenConstantMap_stalk_isIso,
      ``ManuscriptAudit.OpenEtaleExtension.nestedOpenQuotient_stalk_isZero_inside,
      ``ManuscriptAudit.OpenEtaleExtension.nestedOpenQuotientStalkIso,
      ``ManuscriptAudit.OpenEtaleExtension.nestedOpenQuotient_stalk_isZero_outside] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
