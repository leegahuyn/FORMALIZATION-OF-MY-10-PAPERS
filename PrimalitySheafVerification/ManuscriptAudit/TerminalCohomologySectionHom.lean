import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-! The native H⁰ comparison evaluates the actual presheaf adjoint of
a map from the constant free integers at its ordinary generator. -/

namespace ManuscriptAudit.TerminalCohomologySectionHom

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {D : Type*} [Category* D] (J : GrothendieckTopology D)
  [HasSheafify J AddCommGrpCat.{u}] [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]

private abbrev A := AddCommGrpCat.{u}
abbrev integerGroup := AddCommGrpCat.of (ULift.{u} ℤ)
abbrev integerPresheaf := (Functor.const Dᵒᵖ).obj integerGroup.{u}
abbrev integerSheaf := (constantSheaf J A.{u}).obj integerGroup.{u}

private abbrev s := sheafificationAdjunction J A.{u}

variable {T : D} (hT : IsTerminal T)
variable (F : Sheaf J A.{u})

/-- The genuine sheaf morphism associated to a terminal section. -/
def sectionHom (x : F.obj.obj (op T)) : integerSheaf J ⟶ F :=
  Ext.homEquiv₀ ((Sheaf.H.equiv₀ F hT).symm x)

theorem mk₀_sectionHom (x : F.obj.obj (op T)) :
    Ext.mk₀ (sectionHom J hT F x) = (Sheaf.H.equiv₀ F hT).symm x :=
  Ext.mk₀_homEquiv₀_apply _


/-- A map of coefficients sends the map of constant integers to the
map representing the actual image of the given section. -/
theorem sectionHom_map {G : Sheaf J A.{u}} (f : F ⟶ G) (x : F.obj.obj (op T)) :
    sectionHom J hT G (f.hom.app (op T) x) = sectionHom J hT F x ≫ f := by
  have h : Sheaf.H.map f 0 ((Sheaf.H.equiv₀ F hT).symm x) =
      (Sheaf.H.equiv₀ G hT).symm (f.hom.app (op T) x) :=
    Sheaf.H.equiv₀_symm_naturality hT f x
  apply (Ext.mk₀_bijective (integerSheaf J) G).injective
  rw [mk₀_sectionHom, ← Ext.mk₀_comp_mk₀, mk₀_sectionHom]
  exact h.symm

/-- The literal presheaf map associated to a map from the constant integer sheaf. -/
def presheafHom (f : integerSheaf J ⟶ F) : integerPresheaf (D := D) ⟶ F.obj :=
  (s J).homEquiv (integerPresheaf (D := D)) F f

/-- The map from constant integers represents its literal section at the terminal object. -/
theorem evaluate_hom (f : integerSheaf J ⟶ F) :
    Sheaf.H.equiv₀ F hT (Ext.mk₀ f) = (presheafHom J F f).app (op T) (ULift.up 1) := by
  have h : Ext.addEquiv₀ (Ext.mk₀ f) = f := by
    apply (Ext.mk₀_bijective (integerSheaf J) F).injective
    exact Ext.mk₀_addEquiv₀_apply _
  unfold Sheaf.H.equiv₀
  rw [AddEquiv.trans_apply, h, AddEquiv.trans_apply, Adjunction.homAddEquiv_apply]
  change AddCommGrpCat.uliftZMultiplesAddEquiv _
      (((constantPresheafAdj A.{u} hT).comp (s J)).homEquiv integerGroup.{u} F f) = _
  rw [Adjunction.comp_homEquiv]
  change AddCommGrpCat.uliftZMultiplesAddEquiv _
      ((constantPresheafAdj A.{u} hT).homEquiv integerGroup.{u} F.obj (presheafHom J F f)) = _
  rw [Adjunction.homEquiv_unit]
  change AddCommGrpCat.uliftZMultiplesAddEquiv _
      (𝟙 _ ≫ (presheafHom J F f).app (op T)) = _
  rw [Category.id_comp]
  rfl

/-- At every object the literal integer label is the actual restriction
of the given terminal section. -/
theorem sectionHom_evaluation (x : F.obj.obj (op T)) (U : D) :
    (presheafHom J F (sectionHom J hT F x)).app (op U) (ULift.up 1) =
      F.obj.map (hT.from U).op x := by
  let g := presheafHom J F (sectionHom J hT F x)
  have ht : g.app (op T) (ULift.up 1) = x := by
    rw [← evaluate_hom J hT F, mk₀_sectionHom, AddEquiv.apply_symm_apply]
  have h := NatTrans.naturality_apply g (hT.from U).op (ULift.up 1)
  change g.app (op U) (ULift.up 1) =
      F.obj.map (hT.from U).op (g.app (op T) (ULift.up 1)) at h
  exact h.trans (congrArg (F.obj.map (hT.from U).op) ht)

end

end ManuscriptAudit.TerminalCohomologySectionHom

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.TerminalCohomologySectionHom.sectionHom_evaluation
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
