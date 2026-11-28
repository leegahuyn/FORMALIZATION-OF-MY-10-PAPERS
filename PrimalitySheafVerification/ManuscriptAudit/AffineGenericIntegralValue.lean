import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleGenericSectionValue
import PrimalitySheafVerification.ManuscriptAudit.DedekindEtaleGenericDivisor
import PrimalitySheafVerification.ManuscriptAudit.DedekindValuationChangeField

/-! At the actual affine terminal object the generic-section divisor
uses the original function field, through the canonical tensor unitor. -/

namespace ManuscriptAudit.AffineGenericIntegralValue

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open KummerUnitsSheaf SmallEtaleBaseChange GenericEtaleUnitSections OpenEtaleGenericSectionValue
open EtaleTwoOpenHOne AffineEtaleGenericField DedekindEtaleGenericDivisor
open scoped TensorProduct

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (A B F : Type) [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDomain B]
  [Field F] [Algebra A F] [IsFractionRing A F] [Algebra A B] [Algebra.Etale A B]
variable (h : Function.Bijective (algebraMap A B))

private abbrev Y := Spec (CommRingCat.of F)
private abbrev f := Spec.map (CommRingCat.ofHom (algebraMap A F))
private abbrev U := algebraEtaleObject A B
private abbrev W := (etaleBaseChange (f A F)).obj (U A B)
private abbrev T := F ⊗[A] B

def baseEquiv : A ≃ₐ[A] B := AlgEquiv.ofBijective (Algebra.ofId A B) h

private def unitor : T A B F ≃ₐ[A] F :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[A] F) (baseEquiv A B h).symm).trans
    (Algebra.TensorProduct.rid A A F)

private theorem unitor_left (s : F) :
    unitor A B F h (algebraMap F (T A B F) s) = s := by
  change unitor A B F h (s ⊗ₜ[A] (1 : B)) = s
  simp [unitor, Algebra.TensorProduct.rid_tmul]

private theorem unitor_right (s : B) :
    unitor A B F h (algebraMap B (T A B F) s) =
      algebraMap A F ((baseEquiv A B h).symm s) := by
  change unitor A B F h ((1 : F) ⊗ₜ[A] s) = _
  simp [unitor, Algebra.TensorProduct.rid_tmul, Algebra.algebraMap_eq_smul_one]

private def tensorChartIso : (W A B F).left ≅ Spec (CommRingCat.of (T A B F)) :=
  pullbackSymmetry _ _ ≪≫ pullbackSpecIso A F B

private def tensorUnitorSpec : Y F ≅ Spec (CommRingCat.of (T A B F)) :=
  Scheme.Spec.mapIso (unitor A B F h).toRingEquiv.toCommRingCatIso.op

private def nativeChartIso : (W A B F).left ≅ Y F :=
  tensorChartIso A B F ≪≫ (tensorUnitorSpec A B F h).symm

private theorem nativeChartIso_fac :
    (nativeChartIso A B F h).inv ≫ (W A B F).hom = 𝟙 (Y F) := by
  change (_ ≫ (tensorChartIso A B F).inv) ≫ pullback.snd (U A B).hom (f A F) = _
  rw [Category.assoc]
  have hT : (tensorChartIso A B F).inv ≫ pullback.snd (U A B).hom (f A F) =
      Spec.map (CommRingCat.ofHom (algebraMap F (T A B F))) := by
    unfold tensorChartIso
    rw [Iso.trans_inv, Category.assoc, pullbackSymmetry_inv_comp_snd, pullbackSpecIso_inv_fst']
  rw [hT]
  change Spec.map (CommRingCat.ofHom (unitor A B F h).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap F (T A B F))) = _
  rw [← Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap F (T A B F)) ≫ CommRingCat.ofHom (unitor A B F h).toRingHom =
      𝟙 (CommRingCat.of F) := by
    apply CommRingCat.hom_ext
    exact RingHom.ext (unitor_left A B F h)
  rw [h, Spec.map_id]

private def nativeEtaleIso : W A B F ≅ identityObject (Y F) :=
  MorphismProperty.Over.isoMk (nativeChartIso A B F h) (by
    change (nativeChartIso A B F h).hom ≫ 𝟙 _ = (W A B F).hom
    rw [Category.comp_id]
    apply (cancel_epi (nativeChartIso A B F h).inv).mp
    rw [Iso.inv_hom_id, nativeChartIso_fac])

/-- The actual base change of the canonical affine terminal object is
terminal over the generic field. -/
def baseChangeTerminal : IsTerminal (W A B F) :=
  (MorphismProperty.Over.mkIdTerminal @Etale (Y F)).ofIso (nativeEtaleIso A B F h).symm

/-- The actual generic sections on the affine terminal chart are the
native rational units of its given fraction field. -/
def terminalValue : genericUnitSectionGroup A B F ≃+ Additive Fˣ :=
  (genericValue (f A F) (fullCoordinateUnitSheaf (Y F)) (U A B) (baseChangeTerminal A B F h)).trans
    (ringUnits.mapIso (Scheme.ΓSpecIso (CommRingCat.of F))).addCommGroupIsoToAddEquiv

private theorem terminalValue_tensor (x : genericUnitSectionGroup A B F) :
    terminalValue A B F h x = Additive.ofMul (Units.map (unitor A B F h).toRingHom.toMonoidHom
      ((genericUnitSectionsIso A B F).hom x).toMul) := by
  let u := ((baseChangeTerminal A B F h).uniqueUpToIso
    (MorphismProperty.Over.mkIdTerminal @Etale (Y F))).inv
  have hu : u = (nativeEtaleIso A B F h).inv := (baseChangeTerminal A B F h).hom_ext _ _
  apply Additive.ext
  apply Units.ext
  change (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom (u.left.appTop.hom x.toMul.val) =
    (unitor A B F h) ((Scheme.ΓSpecIso (CommRingCat.of (T A B F))).hom.hom
      ((tensorChartIso A B F).inv.appTop.hom x.toMul.val))
  rw [hu]
  let m := CommRingCat.ofHom (unitor A B F h).toRingHom
  let y := (tensorChartIso A B F).inv.appTop.hom x.toMul.val
  have hNaturality : (Spec.map m).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of F)).hom =
      (Scheme.ΓSpecIso (CommRingCat.of (T A B F))).hom ≫ m :=
    Scheme.ΓSpecIso_naturality m
  change (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom
      ((Spec.map m ≫ (tensorChartIso A B F).inv).appTop.hom x.toMul.val) = _
  rw [Scheme.Hom.comp_appTop]
  exact congrArg (fun φ : Γ(Spec (CommRingCat.of (T A B F)), ⊤) ⟶ CommRingCat.of F =>
    φ.hom y) hNaturality

/-- On the actual terminal chart the native divisor map is the principal
cycle of the genuine rational-section value. -/
theorem sectionDivisor_terminal [IsDedekindDomain B] [Algebra B F] [IsFractionRing B F]
    (hBase : ∀ b : B, algebraMap B F b = algebraMap A F ((baseEquiv A B h).symm b))
    (x : genericUnitSectionGroup A B F) :
    sectionDivisor A B F x = DedekindPrincipalDivisor.principalDivisor B F (terminalValue A B F h x) := by
  let L := T A B F
  letI : Field L := (genericFiber_isField A B F).toField
  letI : IsFractionRing B L := genericFiber_isFractionRing A B F
  have hr (b : B) : unitor A B F h (algebraMap B L b) = algebraMap B F b :=
    (unitor_right A B F h b).trans (hBase b).symm
  rw [terminalValue_tensor]
  exact (DedekindValuationChangeField.principalDivisor_map B L F (unitor A B F h).toRingHom hr
    ((genericUnitSectionsIso A B F).hom x)).symm

end

end ManuscriptAudit.AffineGenericIntegralValue

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineGenericIntegralValue.sectionDivisor_terminal
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
