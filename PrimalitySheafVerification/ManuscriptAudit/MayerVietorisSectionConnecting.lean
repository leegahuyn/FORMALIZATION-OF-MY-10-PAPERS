import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
import PrimalitySheafVerification.ManuscriptAudit.EtalePresheafHOneRepresentatives

/-! The native Mayer–Vietoris connecting arrow agrees with the native
cokernel connecting arrow on a pair of actual local lifts. -/

namespace ManuscriptAudit.MayerVietorisSectionConnecting

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open OpenEtaleExtension EtaleCohomologyPresheafZero EtalePresheafHOneRepresentatives

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

universe u
variable {X : Scheme.{u}} (S : X.smallEtaleTopology.MayerVietorisSquare)
private abbrev C := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
private abbrev L := freeEtaleRepresentable X

private def sectionHom (F : C (X := X)) (U : X.Etale) :
    F.obj.obj (op U) →+ ((L (X := X)).obj U ⟶ F) :=
  Ext.addEquiv₀.toAddMonoidHom.comp (equivZero F U).symm.toAddMonoidHom

private theorem mk₀_sectionHom (F : C (X := X)) (U : X.Etale) (x : F.obj.obj (op U)) :
    Ext.mk₀ (sectionHom F U x) = (equivZero F U).symm x :=
  Ext.mk₀_addEquiv₀_apply _

private theorem sectionHom_coeff {F G : C (X := X)} (g : F ⟶ G) (U : X.Etale)
    (x : F.obj.obj (op U)) :
    sectionHom G U (g.hom.app (op U) x) = sectionHom F U x ≫ g := by
  apply (Ext.mk₀_bijective _ _).injective
  rw [mk₀_sectionHom, ← Ext.mk₀_comp_mk₀, mk₀_sectionHom]
  apply (equivZero G U).injective
  rw [AddEquiv.apply_symm_apply, equivZero_coeff, AddEquiv.apply_symm_apply]

private theorem sectionHom_restrict {U V : X.Etale} (a : U ⟶ V) (F : C (X := X))
    (x : F.obj.obj (op V)) :
    sectionHom F U (F.obj.map a.op x) = (L (X := X)).map a ≫ sectionHom F V x := by
  apply (Ext.mk₀_bijective _ _).injective
  rw [mk₀_sectionHom, ← Ext.mk₀_comp_mk₀, mk₀_sectionHom]
  apply (equivZero F U).injective
  change equivZero F U ((equivZero F U).symm _) =
    equivZero F U ((F.cohomologyPresheaf 0).map a.op ((equivZero F V).symm x))
  rw [AddEquiv.apply_symm_apply, equivZero_natural, AddEquiv.apply_symm_apply]

variable {F I : C (X := X)} (i : F ⟶ I) [Mono i]
private abbrev Q := cokernel i
private abbrev seq := ShortComplex.cokernelSequence i
private theorem short_exact : (seq i).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact i) inferInstance inferInstance

variable (z : (Q i).obj.obj (op S.X₄)) (a : I.obj.obj (op S.X₂))
  (b : I.obj.obj (op S.X₃)) (w : F.obj.obj (op S.X₁))
variable (ha : (cokernel.π i).hom.app (op S.X₂) a = (Q i).obj.map S.f₂₄.op z)
  (hb : (cokernel.π i).hom.app (op S.X₃) b = (Q i).obj.map S.f₃₄.op z)
  (hw : I.obj.map S.f₁₂.op a - I.obj.map S.f₁₃.op b = i.hom.app (op S.X₁) w)

private def comparison : S.shortComplex ⟶ seq i where
  τ₁ := sectionHom F S.X₁ w
  τ₂ := biprod.desc (sectionHom I S.X₂ a) (sectionHom I S.X₃ b)
  τ₃ := sectionHom (Q i) S.X₄ z
  comm₁₂ := by
    symm
    change biprod.lift ((L (X := X)).map S.f₁₂) (- (L (X := X)).map S.f₁₃) ≫
      biprod.desc (sectionHom I S.X₂ a) (sectionHom I S.X₃ b) =
        sectionHom F S.X₁ w ≫ i
    rw [biprod.lift_desc, Preadditive.neg_comp, ← sub_eq_add_neg,
      ← sectionHom_restrict, ← sectionHom_restrict, ← map_sub, hw, sectionHom_coeff]
  comm₂₃ := by
    change biprod.desc (sectionHom I S.X₂ a) (sectionHom I S.X₃ b) ≫ cokernel.π i =
      biprod.desc ((L (X := X)).map S.f₂₄) ((L (X := X)).map S.f₃₄) ≫ sectionHom (Q i) S.X₄ z
    apply biprod.hom_ext'
    · simp only [biprod.inl_desc_assoc]
      rw [← sectionHom_coeff, ← sectionHom_restrict, ha]
    · simp only [biprod.inr_desc_assoc]
      rw [← sectionHom_coeff, ← sectionHom_restrict, hb]

/-- If the actual two sections lift the global cokernel section and
differ by the genuine overlap section, their two connecting classes agree. -/
theorem connectingAt_eq_mv :
    connectingAt i S.X₄ z = S.δ F 0 1 rfl ((equivZero F S.X₁).symm w) := by
  let g := comparison S i z a b w ha hb hw
  have h := S.shortComplex_shortExact.extClass_naturality (short_exact i) g
  change S.shortComplex_shortExact.extClass.comp (Ext.mk₀ (sectionHom F S.X₁ w)) (add_zero 1) =
    (Ext.mk₀ (sectionHom (Q i) S.X₄ z)).comp (short_exact i).extClass (zero_add 1) at h
  rw [mk₀_sectionHom, mk₀_sectionHom] at h
  exact h.symm

end

end ManuscriptAudit.MayerVietorisSectionConnecting

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.MayerVietorisSectionConnecting.connectingAt_eq_mv
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
