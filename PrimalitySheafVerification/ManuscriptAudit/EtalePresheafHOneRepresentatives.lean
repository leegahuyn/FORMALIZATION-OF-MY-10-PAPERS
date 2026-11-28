import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleCohomologyPresheafZero
import PrimalitySheafVerification.ManuscriptAudit.SheafH1Descent

/-! The actual ambient degree-one étale cohomology presheaf is represented
by cokernel sections of an injective embedding, with genuine restriction. -/

namespace ManuscriptAudit.EtalePresheafHOneRepresentatives

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open OpenEtaleExtension EtaleCohomologyPresheafZero

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

universe u
variable {X : Scheme.{u}}
private abbrev C := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
private abbrev Q (U : X.Etale) := (freeEtaleRepresentable X).obj U

variable {F I : C (X := X)} (i : F ⟶ I) [Mono i]

private abbrev seq := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)

private theorem short_exact : (seq i).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel i)
  mono_f := inferInstance
  epi_g := inferInstance

/-- The connecting map of a genuine injective embedding at a native
ambient small étale object. -/
def connectingAt (U : X.Etale) : (cokernel i).obj.obj (op U) →+ F.H' 1 U :=
  ((short_exact i).extClass.postcomp (Q U) (zero_add 1)).comp
    (equivZero (cokernel i) U).symm.toAddMonoidHom

/-- Every degree-one native presheaf class has a cokernel-section representative. -/
theorem connectingAt_surjective [Injective I] (U : X.Etale) :
    Function.Surjective (connectingAt i U) := by
  intro x
  have hx : x.comp (Ext.mk₀ (seq i).f) (add_zero 1) = 0 := Ext.eq_zero_of_injective _
  have h := Ext.covariant_sequence_exact₁' (Q U) (short_exact i) 0 1 rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  obtain ⟨z, hz⟩ := (h x).1 hx
  refine ⟨equivZero (cokernel i) U z, ?_⟩
  change ((short_exact i).extClass.postcomp (Q U) (zero_add 1))
    ((equivZero (cokernel i) U).symm (equivZero (cokernel i) U z)) = x
  rw [AddEquiv.symm_apply_apply]
  exact hz

/-- Actual connecting-section representatives commute with the native
étale cohomology presheaf restriction maps, including both chart arms
and the overlap of a Mayer–Vietoris square. -/
theorem connectingAt_natural {U V : X.Etale} (f : U ⟶ V)
    (x : (cokernel i).obj.obj (op V)) :
    (F.cohomologyPresheaf 1).map f.op (connectingAt i V x) =
      connectingAt i U ((cokernel i).obj.map f.op x) := by
  let y := (equivZero (cokernel i) V).symm x
  let e := Ext.mk₀ ((freeEtaleRepresentable X).map f)
  let δ := (short_exact i).extClass
  have h0 : ((cokernel i).cohomologyPresheaf 0).map f.op y =
      (equivZero (cokernel i) U).symm ((cokernel i).obj.map f.op x) := by
    apply (equivZero (cokernel i) U).injective
    simp only [equivZero_natural, y, AddEquiv.apply_symm_apply]
  change e.comp (y.comp δ (zero_add 1)) (zero_add 1) =
    ((equivZero (cokernel i) U).symm ((cokernel i).obj.map f.op x)).comp δ (zero_add 1)
  rw [← h0]
  change e.comp (y.comp δ (zero_add 1)) (zero_add 1) =
    (e.comp y (zero_add 0)).comp δ (zero_add 1)
  exact (Ext.comp_assoc_of_second_deg_zero e y δ (zero_add 1)).symm


private abbrev freeSheafAdj :=
  (Adjunction.whiskerRight X.Etaleᵒᵖ AddCommGrpCat.adj).comp
    (sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u})

/-- Evaluating a native degree-zero presheaf class commutes with each
map in the sheaf coefficient variable. -/
theorem equivZero_map_sheaf {A B : C (X := X)} (g : A ⟶ B) (U : X.Etale)
    (x : A.H' 0 U) :
    equivZero B U ((Ext.mk₀ g).postcomp (Q U) (add_zero 0) x) =
      g.hom.app (op U) (equivZero A U x) := by
  let f := Ext.addEquiv₀ x
  have he : Ext.addEquiv₀ ((Ext.mk₀ g).postcomp (Q U) (add_zero 0) x) = f ≫ g := by
    apply (Ext.mk₀_bijective _ _).injective
    rw [Ext.mk₀_addEquiv₀_apply, ← Ext.mk₀_comp_mk₀]
    change x.comp (Ext.mk₀ g) (add_zero 0) =
      (Ext.mk₀ (Ext.addEquiv₀ x)).comp (Ext.mk₀ g) (zero_add 0)
    rw [Ext.mk₀_addEquiv₀_apply]
  change yonedaEquiv (((freeSheafAdj (X := X)).homEquiv (yoneda.obj U) B)
    (Ext.addEquiv₀ ((Ext.mk₀ g).postcomp (Q U) (add_zero 0) x))) =
    g.hom.app (op U)
      (yonedaEquiv (((freeSheafAdj (X := X)).homEquiv (yoneda.obj U) A) f))
  calc
    _ = yonedaEquiv (((freeSheafAdj (X := X)).homEquiv (yoneda.obj U) B) (f ≫ g)) :=
      congrArg (fun q : Q U ⟶ B =>
        yonedaEquiv (((freeSheafAdj (X := X)).homEquiv (yoneda.obj U) B) q)) he
    _ = _ := by
      rw [(freeSheafAdj (X := X)).homEquiv_naturality_right, yonedaEquiv_comp] <;> rfl

/-- At each actual étale object a connecting class is zero exactly when its
cokernel section is the image of an actual section of the middle sheaf. -/
theorem connectingAt_eq_zero_iff (U : X.Etale) (x : (cokernel i).obj.obj (op U)) :
    connectingAt i U x = 0 ↔ ∃ z : I.obj.obj (op U), (cokernel.π i).hom.app (op U) z = x := by
  let g := (Ext.mk₀ (cokernel.π i)).postcomp (Q U) (add_zero 0)
  let a := equivZero (cokernel i) U
  let b := equivZero I U
  have h := Ext.covariant_sequence_exact₃' (Q U) (short_exact i) 0 1 rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  constructor
  · intro hx
    obtain ⟨z, hz⟩ := (h (a.symm x)).1 hx
    have hz' : g z = a.symm x := hz
    refine ⟨b z, ?_⟩
    exact (equivZero_map_sheaf (cokernel.π i) U z).symm.trans
      ((congrArg a hz').trans (a.apply_symm_apply x))
  · rintro ⟨z, rfl⟩
    apply (h _).2
    refine ⟨b.symm z, ?_⟩
    apply a.injective
    change a (g (b.symm z)) = a (a.symm ((cokernel.π i).hom.app (op U) z))
    rw [equivZero_map_sheaf, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

end

end ManuscriptAudit.EtalePresheafHOneRepresentatives

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtalePresheafHOneRepresentatives.connectingAt_surjective,
      ``ManuscriptAudit.EtalePresheafHOneRepresentatives.connectingAt_natural,
      ``ManuscriptAudit.EtalePresheafHOneRepresentatives.connectingAt_eq_zero_iff] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
