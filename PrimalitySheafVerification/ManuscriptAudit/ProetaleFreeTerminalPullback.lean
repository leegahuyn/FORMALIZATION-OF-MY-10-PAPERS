import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Adjunction.Unique
import PrimalitySheafVerification.ManuscriptAudit.ProetaleFreeExtPullback
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAffineUnitPullback

/-! The terminal free-chart pullback equals the native constant-integer
representative used in Mathlib's ordinary sheaf cohomology. -/

namespace ManuscriptAudit.ProetaleFreeTerminalPullback

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open ProetaleBaseChange (baseChange directImage)
open ProetaleInverseImage (inverseImage adjunction constantInverseImageIso)
open ProetaleMayerVietorisRepresentable (nativeFree terminalIso)
open ProetaleFreeExtPullback (chartIso map_section map_mk)
open ProetaleSchemeCohomologyPullback (pullback)
open EtaleProetaleFreeRepresentable (proSections)
open ProetaleAffineUnitPullback (terminal_restrict)
open ProetaleOpenLocalLifts (identityObject)
open ProetaleOpenExtAdjunction (integers)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{1}
private abbrev M := AddCommGrpCat.of (ULift.{1} ℤ)
private abbrev T := identityObject
private abbrev hT (X : Scheme.{0}) : IsTerminal (T X) :=
  MorphismProperty.Over.mkIdTerminal @WeaklyEtale X

private abbrev gen {X : Scheme.{0}} {U : X.ProEt} (hU : IsTerminal U) :=
  Sheaf.H.equiv₀ (integers X) hU (Ext.mk₀ (𝟙 (integers X)))

private theorem gen_formula {X : Scheme.{0}} {U : X.ProEt} (hU : IsTerminal U) :
    gen hU = ((constantSheafAdj (Scheme.ProEt.topology X) A hU).homEquiv M (integers X))
      (𝟙 (integers X)) (⟨1⟩ : ULift.{1} ℤ) := by
  have h : Ext.addEquiv₀ (Ext.mk₀ (𝟙 (integers X))) = 𝟙 (integers X) :=
    Ext.addEquiv₀.apply_symm_apply _
  change ((constantSheafAdj (Scheme.ProEt.topology X) A hU).homEquiv M (integers X))
    (Ext.addEquiv₀ (Ext.mk₀ (𝟙 (integers X)))) (⟨1⟩ : ULift.{1} ℤ) = _
  rw [h]

set_option maxHeartbeats 5500000 in
private theorem terminalIso_section (X : Scheme.{0}) :
    proSections X (T X) (integers X) (terminalIso X).hom = gen (hT X) := by
  rw [gen_formula]
  let g := ((constantSheafAdj (Scheme.ProEt.topology X) A (hT X)).homEquiv M (integers X))
    (𝟙 (integers X)) (⟨1⟩ : ULift.{1} ℤ)
  change proSections X (T X) (integers X) ((proSections X (T X) (integers X)).symm g) = _
  exact Equiv.apply_symm_apply _ _

variable {X Y : Scheme.{0}} (f : X ⟶ Y)
  (e : (baseChange f).obj (T Y) ≅ T X)

private abbrev b := (constantInverseImageIso f).app M

set_option maxHeartbeats 6700000 in
private theorem generator_pullback :
    let a := ((adjunction f).homEquiv (integers Y) (integers X)) (b f).hom
    (integers X).obj.map e.inv.op (a.hom.app (op (T Y)) (gen (hT Y))) = gen (hT X) := by
  let R := directImage f A
  let ad := adjunction f
  let U := (baseChange f).obj (T Y)
  let hU : IsTerminal U := IsTerminal.isTerminalObj (baseChange f) (T Y) (hT Y)
  let sy := constantSheafAdj (Scheme.ProEt.topology Y) A (hT Y)
  let sx := constantSheafAdj (Scheme.ProEt.topology X) A hU
  let c := sy.comp ad
  let a : integers Y ⟶ R.obj (integers X) :=
    (ad.homEquiv _ _) (b f).hom
  have h₀ : (sy.homEquiv M (R.obj (integers X))) a = sx.unit.app M := by
    change (c.homEquiv M (integers X)) ((c.leftAdjointUniq sx).hom.app M) = _
    exact Adjunction.homEquiv_leftAdjointUniq_hom_app c sx M
  have h₁ : (sy.homEquiv M (integers Y)) (𝟙 (integers Y)) ≫ a.hom.app (op (T Y)) =
      (sx.homEquiv M (integers X)) (𝟙 (integers X)) := by
    have h := sy.homEquiv_naturality_right (𝟙 (integers Y)) a
    rw [Category.id_comp] at h
    change (sy.homEquiv M (R.obj (integers X))) a =
      (sy.homEquiv M (integers Y)) (𝟙 (integers Y)) ≫ a.hom.app (op (T Y)) at h
    rw [← h, h₀, sx.homEquiv_unit, Functor.map_id, Category.comp_id]
  have hs : a.hom.app (op (T Y)) (gen (hT Y)) = gen hU := by
    rw [gen_formula, gen_formula]
    exact ConcreteCategory.congr_hom h₁ (⟨1⟩ : ULift.{1} ℤ)
  change (integers X).obj.map e.inv.op (a.hom.app (op (T Y)) (gen (hT Y))) = _
  rw [hs]
  exact terminal_restrict hU (hT X) e.inv (integers X) _

set_option maxHeartbeats 6500000 in
/-- The terminal comparison uses the actual constant integer coefficient. -/
theorem terminal_comparison :
    (chartIso f e).inv ≫ (inverseImage f).map (terminalIso Y).hom ≫ (b f).hom =
      (terminalIso X).hom := by
  let ad := adjunction f
  let a := (ad.homEquiv (integers Y) (integers X)) (b f).hom
  let g := (terminalIso Y).hom
  have he : (ad.homEquiv (integers Y) (integers X)).symm a = (b f).hom :=
    (ad.homEquiv _ _).symm_apply_apply _
  have h := map_section f e a g
  rw [he, map_mk] at h
  let q := (chartIso f e).inv ≫ (inverseImage f).map g ≫ (b f).hom
  have hq : Ext.addEquiv₀ (Ext.mk₀ q) = q := Ext.addEquiv₀.apply_symm_apply _
  change proSections X (T X) (integers X) (Ext.addEquiv₀ (Ext.mk₀ q)) =
    (integers X).obj.map e.inv.op (a.hom.app (op (T Y)) (proSections Y (T Y) (integers Y) g)) at h
  rw [hq, terminalIso_section, generator_pullback f e] at h
  apply (proSections X (T X) (integers X)).injective
  exact h.trans (terminalIso_section X).symm

private theorem terminal_precomp :
    (terminalIso X).inv ≫ (chartIso f e).inv ≫ (inverseImage f).map (terminalIso Y).hom = (b f).inv := by
  apply (cancel_mono (b f).hom).mp
  rw [Category.assoc, Category.assoc, terminal_comparison f e, Iso.inv_hom_id, Iso.inv_hom_id]

set_option maxHeartbeats 6700000 in
/-- The exact terminal chart pullback agrees with the ordinary native pullback in every degree. -/
theorem map_terminal {F : Sheaf (Scheme.ProEt.topology Y) A} {G : Sheaf (Scheme.ProEt.topology X) A}
    (g : (inverseImage f).obj F ⟶ G) (n : ℕ) (u : Sheaf.H F n) :
    (Ext.mk₀ (terminalIso X).inv).comp
      (ProetaleFreeExtPullback.map f e g n ((Ext.mk₀ (terminalIso Y).hom).comp u (zero_add n)))
      (zero_add n) =
    Sheaf.H.map g n (pullback f F n u) := by
  let L := inverseImage f
  let x := (terminalIso X).inv
  let y := (terminalIso Y).hom
  let a := (chartIso f e).inv
  change (Ext.mk₀ x).comp (((Ext.mk₀ a).comp
      (((Ext.mk₀ y).comp u (zero_add n)).mapExactFunctor L) (zero_add n)).comp
      (Ext.mk₀ g) (add_zero n)) (zero_add n) =
    ((Ext.mk₀ (b f).inv).comp (u.mapExactFunctor L) (zero_add n)).comp (Ext.mk₀ g) (add_zero n)
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  rw [← Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀_assoc, Ext.mk₀_comp_mk₀_assoc,
    Category.assoc, terminal_precomp f e]

end
end ManuscriptAudit.ProetaleFreeTerminalPullback

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``ManuscriptAudit.ProetaleFreeTerminalPullback.terminal_comparison,
      ``ManuscriptAudit.ProetaleFreeTerminalPullback.map_terminal] do
    let ax ← collectAxioms n
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{n} depends on unexpected axioms {ax}"
    logInfo m!"{n} uses {ax}"
