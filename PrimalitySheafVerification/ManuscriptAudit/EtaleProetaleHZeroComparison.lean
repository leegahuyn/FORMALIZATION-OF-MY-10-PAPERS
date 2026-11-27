import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleProetaleUnitComparison

/-! The actual comparison of units is an isomorphism in degree zero. -/

namespace ManuscriptAudit.EtaleProetaleHZeroComparison

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open EtaleProetaleInverseImage EtaleProetaleCohomologyMap EtaleProetaleUnitComparison

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{0})

private abbrev C := Sheaf X.smallEtaleTopology AddCommGrpCat.{1}
private abbrev D := Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{1}

local instance etaleHasExt : HasExt.{1} (C X) := by
  letI : EssentiallySmall.{1} X.Etale :=
    EssentiallySmall.mk' (AsSmall.equiv : X.Etale ≌ AsSmall.{0} X.Etale)
  letI := Sheaf.isGrothendieckAbelian_of_essentiallySmall X.smallEtaleTopology AddCommGrpCat.{1}
  exact IsGrothendieckAbelian.hasExt _

local instance inverseImageAdditive : (inverseImage X).Additive :=
  Functor.additive_of_preserves_binary_products (inverseImage X)

private abbrev integers := AddCommGrpCat.of (ULift.{1} ℤ)
private abbrev ZE := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{1}).obj integers
private abbrev ZP := (constantSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{1}).obj integers
private abbrev integersIso : (inverseImage X).obj (ZE X) ≅ ZP X :=
  (constantInverseImageIso X).app integers

private def homComparison (F : D X) (E : C X) (j : (directImage X).obj F ≅ E) :
    (ZE X ⟶ E) ≃ (ZP X ⟶ F) where
  toFun f := (integersIso X).inv ≫ ((adjunction X).homEquiv (ZE X) F).symm (f ≫ j.inv)
  invFun g := ((adjunction X).homEquiv (ZE X) F) ((integersIso X).hom ≫ g) ≫ j.hom
  left_inv f := by simp [Category.assoc]
  right_inv g := by simp [Category.assoc]

private def comparison (F : D X) (E : C X) (j : (directImage X).obj F ≅ E) :
    Sheaf.H E 0 →+ Sheaf.H F 0 :=
  (Sheaf.H.map (((adjunction X).homEquiv E F).symm j.inv) 0).comp (pullback X E 0)

private theorem comparison_mk₀ (F : D X) (E : C X) (j : (directImage X).obj F ≅ E)
    (f : ZE X ⟶ E) :
    comparison X F E j (Ext.mk₀ f) = Ext.mk₀ (homComparison X F E j f) := by
  change ((Ext.mk₀ (integersIso X).inv).comp
      ((Ext.mk₀ f).mapExactFunctor (inverseImage X)) (zero_add 0)).comp
      (Ext.mk₀ (((adjunction X).homEquiv E F).symm j.inv)) (add_zero 0) = _
  rw [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀]
  congr 1
  change ((integersIso X).inv ≫ (inverseImage X).map f) ≫
      ((adjunction X).homEquiv E F).symm j.inv =
    (integersIso X).inv ≫ ((adjunction X).homEquiv (ZE X) F).symm (f ≫ j.inv)
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, Functor.map_comp]
  simp only [Category.assoc]

private theorem comparison_bijective (F : D X) (E : C X) (j : (directImage X).obj F ≅ E) :
    Function.Bijective (comparison X F E j) := by
  let h := (Ext.homEquiv₀.trans (homComparison X F E j)).trans Ext.homEquiv₀.symm
  have he : (comparison X F E j : Sheaf.H E 0 → Sheaf.H F 0) = h := by
    funext a
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective (ZE X) E).surjective a
    rw [comparison_mk₀]
    simpa only [h, Equiv.trans_apply, Ext.homEquiv₀, Equiv.symm_symm,
      Equiv.ofBijective_apply, Equiv.symm_apply_apply]
  rw [he]
  exact h.bijective

theorem units_comparison_bijective :
    Function.Bijective (unitCohomologyComparison X 0) :=
  comparison_bijective X (proetaleUnits X) (etaleUnits X) (directImageUnitsIso X)

def unitsComparison :
    Sheaf.H (etaleUnits X) 0 ≃+ Sheaf.H (proetaleUnits X) 0 :=
  AddEquiv.ofBijective (unitCohomologyComparison X 0) (units_comparison_bijective X)

end
end ManuscriptAudit.EtaleProetaleHZeroComparison

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleProetaleHZeroComparison.units_comparison_bijective,
      ``ManuscriptAudit.EtaleProetaleHZeroComparison.unitsComparison] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
