import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleExtensionCounit
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleExtensionExact
import PrimalitySheafVerification.ManuscriptAudit.PushoutShortExact

/-! A short exact extension on an open lifts to an ambient short exact
extension whenever its kernel comes by restriction from the ambient
scheme. The new extension is the pushout of the exact extension by zero. -/

namespace ManuscriptAudit.OpenEtaleExtendShortExact

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open OpenEtaleExtension PushoutShortExact

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

private abbrev C := AddCommGrpCat.{u}

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

private abbrev E := extensionByZero j C.{u}
private abbrev R := restriction j C.{u}

attribute [local instance] extensionByZero_additive restriction_additive

/-- Restricting extension by zero back to the open recovers the sheaf. -/
theorem extensionUnit_isIso (F : Sheaf U.smallEtaleTopology C.{u}) :
    IsIso ((abelianExtensionByZeroAdjunction j).unit.app F) := by
  let geometricPoint (x : U) : Spec (.of (SeparableClosure (U.residueField x))) ⟶ U :=
    (Scheme.SpecToEquivOfField (SeparableClosure (U.residueField x)) U).2
      ⟨x, CommRingCat.ofHom (algebraMap (U.residueField x) _)⟩
  let P := ObjectProperty.ofObj (fun x : U => Scheme.pointSmallEtale (geometricPoint x))
  have hP : P.IsConservativeFamilyOfPoints :=
    Scheme.isConservativeFamilyOfPoints_pointSmallEtale' U
  let η := (abelianExtensionByZeroAdjunction j).unit.app F
  letI : ∀ p : P.FullSubcategory, IsIso (p.obj.sheafFiber.map η) := fun p => by
    obtain ⟨x, hx⟩ := (ObjectProperty.ofObj_iff
      (fun x : U => Scheme.pointSmallEtale (geometricPoint x)) p.obj).mp p.property
    rw [← hx]
    exact extensionUnit_stalk_isIso j (geometricPoint x) F
  exact (hP.jointlyReflectIsomorphisms C.{u}).isIso η

variable (S : ShortComplex (Sheaf U.smallEtaleTopology C.{u}))
variable (F : Sheaf X.smallEtaleTopology C.{u})
variable (e : S.X₁ ≅ (R j).obj F)

def kernelMap : (S.map (E j)).X₁ ⟶ F :=
  ((abelianExtensionByZeroAdjunction j).homEquiv S.X₁ F).symm e.hom

/-- An actual ambient extension whose kernel is F and whose quotient is
the extension by zero of the original quotient. -/
def extended : ShortComplex (Sheaf X.smallEtaleTopology C.{u}) :=
  pushKernel (S.map (E j)) (kernelMap j S F e)

theorem extended_shortExact (hS : S.ShortExact) : (extended j S F e).ShortExact := by
  letI : PreservesFiniteLimits (E j) := (extensionByZero_exact j).1
  letI : PreservesFiniteColimits (E j) := (extensionByZero_exact j).2
  exact pushKernel_shortExact _ _ (hS.map_of_exact (E j))

private def unitShortComplex : S ⟶ (S.map (E j)).map (R j) where
  τ₁ := (abelianExtensionByZeroAdjunction j).unit.app S.X₁
  τ₂ := (abelianExtensionByZeroAdjunction j).unit.app S.X₂
  τ₃ := (abelianExtensionByZeroAdjunction j).unit.app S.X₃
  comm₁₂ := by
    simpa using ((abelianExtensionByZeroAdjunction j).unit.naturality S.f).symm
  comm₂₃ := by
    simpa using ((abelianExtensionByZeroAdjunction j).unit.naturality S.g).symm

def restrictedExtensionMap :
    S ⟶ (extended j S F e).map (R j) :=
  unitShortComplex j S ≫ (R j).mapShortComplex.map
    (toPushKernel (S.map (E j)) (kernelMap j S F e))

theorem restrictedExtensionMap_left :
    (restrictedExtensionMap j S F e).τ₁ = e.hom := by
  let a := abelianExtensionByZeroAdjunction j
  change a.unit.app S.X₁ ≫ (R j).map (kernelMap j S F e) = e.hom
  exact (a.homEquiv S.X₁ F).apply_symm_apply e.hom

theorem restrictedExtensionMap_right :
    (restrictedExtensionMap j S F e).τ₃ =
      (abelianExtensionByZeroAdjunction j).unit.app S.X₃ := by
  change (abelianExtensionByZeroAdjunction j).unit.app S.X₃ ≫
    (R j).map (𝟙 ((E j).obj S.X₃)) = _
  rw [(R j).map_id]
  exact Category.comp_id ((abelianExtensionByZeroAdjunction j).unit.app S.X₃)

/-- The native ambient extension restricts back to the original short exact sequence. -/
def restrictedExtensionIso (hS : S.ShortExact) :
    S ≅ (extended j S F e).map (R j) := by
  let φ := restrictedExtensionMap j S F e
  haveI : IsIso φ.τ₁ := by
    change IsIso (restrictedExtensionMap j S F e).τ₁
    rw [restrictedExtensionMap_left]
    infer_instance
  haveI : IsIso φ.τ₃ := by
    change IsIso (restrictedExtensionMap j S F e).τ₃
    rw [restrictedExtensionMap_right]
    exact extensionUnit_isIso j S.X₃
  letI : PreservesFiniteLimits (R j) := (restriction_exact j).1
  letI : PreservesFiniteColimits (R j) := (restriction_exact j).2
  have hT : ((extended j S F e).map (R j)).ShortExact :=
    (extended_shortExact j S F e hS).map_of_exact (R j)
  letI : IsIso φ.τ₂ := ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ φ hS hT
  letI : IsIso φ := ShortComplex.isIso_of_isIso φ
  exact asIso φ

end
end ManuscriptAudit.OpenEtaleExtendShortExact

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.OpenEtaleExtendShortExact.extensionUnit_isIso,
      ``ManuscriptAudit.OpenEtaleExtendShortExact.extended_shortExact,
      ``ManuscriptAudit.OpenEtaleExtendShortExact.restrictedExtensionIso] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
