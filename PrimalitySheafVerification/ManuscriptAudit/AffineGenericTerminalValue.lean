import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleGenericSectionValue
import PrimalitySheafVerification.ManuscriptAudit.DedekindEtaleGenericDivisor
import PrimalitySheafVerification.ManuscriptAudit.DedekindValuationChangeField

/-! At the actual affine terminal object the generic-section divisor
uses the original function field, through the canonical tensor unitor. -/

namespace ManuscriptAudit.AffineGenericTerminalValue

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open KummerUnitsSheaf SmallEtaleBaseChange GenericEtaleUnitSections OpenEtaleGenericSectionValue
open EtaleTwoOpenHOne AffineEtaleGenericField DedekindEtaleGenericDivisor
open scoped TensorProduct

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (A F : Type) [CommRing A] [IsDedekindDomain A] [Field F] [Algebra A F] [IsFractionRing A F]

private abbrev Y := Spec (CommRingCat.of F)
private abbrev f := Spec.map (CommRingCat.ofHom (algebraMap A F))
private abbrev U := algebraEtaleObject A A
private abbrev W := (etaleBaseChange (f A F)).obj (U A)
private abbrev T := F ⊗[A] A
private abbrev rid := Algebra.TensorProduct.rid A F F

private def tensorChartIso : (W A F).left ≅ Spec (CommRingCat.of (T A F)) :=
  pullbackSymmetry _ _ ≪≫ pullbackSpecIso A F A

private def tensorUnitorSpec : Y F ≅ Spec (CommRingCat.of (T A F)) :=
  Scheme.Spec.mapIso (rid A F).toRingEquiv.toCommRingCatIso.op

private def nativeChartIso : (W A F).left ≅ Y F :=
  tensorChartIso A F ≪≫ (tensorUnitorSpec A F).symm

private theorem nativeChartIso_fac :
    (nativeChartIso A F).inv ≫ (W A F).hom = 𝟙 (Y F) := by
  change (_ ≫ (tensorChartIso A F).inv) ≫ pullback.snd (U A).hom (f A F) = _
  rw [Category.assoc]
  have hT : (tensorChartIso A F).inv ≫ pullback.snd (U A).hom (f A F) =
      Spec.map (CommRingCat.ofHom (algebraMap F (T A F))) := by
    unfold tensorChartIso
    rw [Iso.trans_inv, Category.assoc, pullbackSymmetry_inv_comp_snd, pullbackSpecIso_inv_fst']
  rw [hT]
  change Spec.map (CommRingCat.ofHom (rid A F).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap F (T A F))) = _
  rw [← Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap F (T A F)) ≫ CommRingCat.ofHom (rid A F).toRingHom =
      𝟙 (CommRingCat.of F) := by
    apply CommRingCat.hom_ext
    exact RingHom.ext (rid A F).commutes
  rw [h, Spec.map_id]

private def nativeEtaleIso : W A F ≅ identityObject (Y F) :=
  MorphismProperty.Over.isoMk (nativeChartIso A F) (by
    change (nativeChartIso A F).hom ≫ 𝟙 _ = (W A F).hom
    rw [Category.comp_id]
    apply (cancel_epi (nativeChartIso A F).inv).mp
    rw [Iso.inv_hom_id, nativeChartIso_fac])

/-- The actual base change of the canonical affine terminal object is
terminal over the generic field. -/
def baseChangeTerminal : IsTerminal (W A F) :=
  (MorphismProperty.Over.mkIdTerminal @Etale (Y F)).ofIso (nativeEtaleIso A F).symm

/-- The actual generic sections on the affine terminal chart are the
native rational units of its given fraction field. -/
def terminalValue : genericUnitSectionGroup A A F ≃+ Additive Fˣ :=
  (genericValue (f A F) (fullCoordinateUnitSheaf (Y F)) (U A) (baseChangeTerminal A F)).trans
    (ringUnits.mapIso (Scheme.ΓSpecIso (CommRingCat.of F))).addCommGroupIsoToAddEquiv

private theorem terminalValue_tensor (x : genericUnitSectionGroup A A F) :
    terminalValue A F x = Additive.ofMul (Units.map (rid A F).toRingHom.toMonoidHom
      ((genericUnitSectionsIso A A F).hom x).toMul) := by
  let u := ((baseChangeTerminal A F).uniqueUpToIso
    (MorphismProperty.Over.mkIdTerminal @Etale (Y F))).inv
  have hu : u = (nativeEtaleIso A F).inv := (baseChangeTerminal A F).hom_ext _ _
  apply Additive.ext
  apply Units.ext
  change (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom (u.left.appTop.hom x.toMul.val) =
    (rid A F) ((Scheme.ΓSpecIso (CommRingCat.of (T A F))).hom.hom
      ((tensorChartIso A F).inv.appTop.hom x.toMul.val))
  rw [hu]
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (rid A F).toRingHom)
  change _ = _ at h
  have hx := congrArg (fun φ : Γ(Spec (CommRingCat.of (T A F)), ⊤) ⟶ CommRingCat.of F =>
    φ.hom ((tensorChartIso A F).inv.appTop.hom x.toMul.val)) h
  change _ = _ at hx
  simpa only [nativeEtaleIso, nativeChartIso, Iso.trans_inv, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply] using hx

/-- On the actual terminal chart the native divisor map is the principal
cycle of the genuine rational-section value. -/
theorem sectionDivisor_terminal (x : genericUnitSectionGroup A A F) :
    sectionDivisor A A F x = DedekindPrincipalDivisor.principalDivisor A F (terminalValue A F x) := by
  let L := T A F
  letI : Field L := (genericFiber_isField A A F).toField
  letI : IsFractionRing A L := genericFiber_isFractionRing A A F
  have hr (a : A) : (rid A F) (algebraMap A L a) = algebraMap A F a := by
    change Algebra.TensorProduct.rid A F F ((1 : F) ⊗ₜ[A] a) = _
    rw [Algebra.TensorProduct.rid_tmul, Algebra.algebraMap_eq_smul_one]
  rw [terminalValue_tensor]
  exact (DedekindValuationChangeField.principalDivisor_map A L F (rid A F).toRingHom hr
    ((genericUnitSectionsIso A A F).hom x)).symm

end

end ManuscriptAudit.AffineGenericTerminalValue

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineGenericTerminalValue.sectionDivisor_terminal
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
