import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Adjunction.Unique
import PrimalitySheafVerification.ManuscriptAudit.ProetaleSchemeCohomologyPullback

/-! Degree zero of the actual cohomology pullback is the map of sections
under its defining direct-image adjunction. -/

namespace ManuscriptAudit.ProetaleSchemePullbackHZero

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open ProetaleInverseImage (inverseImage adjunction constantInverseImageIso)
open ProetaleBaseChange (baseChange directImage)
open ProetaleSchemeCohomologyPullback (pullback mapOfDirectImage)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{1}
private abbrev C (X : Scheme.{0}) := Sheaf (Scheme.ProEt.topology X) A
private abbrev M := AddCommGrpCat.of (ULift.{1} ℤ)
private abbrev Z (X : Scheme.{0}) := (constantSheaf (Scheme.ProEt.topology X) A).obj M

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

private abbrev T (S : Scheme.{0}) := Scheme.ProEt.mk (𝟙 S)
private abbrev hT (S : Scheme.{0}) : IsTerminal (T S) :=
  MorphismProperty.Over.mkIdTerminal @WeaklyEtale S

private abbrev U := (baseChange f).obj (T Y)
private abbrev hU : IsTerminal (U f) :=
  IsTerminal.isTerminalObj (baseChange f) (T Y) (hT Y)

/-- The literal degree-zero pullback evaluates the coefficient's direct-image map. -/
theorem equivZero_mapOfDirectImage {F : C Y} {G : C X}
    (a : F ⟶ (directImage f A).obj G) (x : Sheaf.H F 0) :
    Sheaf.H.equiv₀ G (hU f) (mapOfDirectImage f a 0 x) =
      a.hom.app (op (T Y)) (Sheaf.H.equiv₀ F (hT Y) x) := by
  obtain ⟨b, rfl⟩ := (Ext.mk₀_bijective (Z Y) F).surjective x
  let L := inverseImage f
  let R := directImage f A
  let adj := adjunction f
  let aX := constantSheafAdj (Scheme.ProEt.topology X) A (hU f)
  let aY := constantSheafAdj (Scheme.ProEt.topology Y) A (hT Y)
  let c := aY.comp adj
  let k : L.obj (Z Y) ≅ Z X := (constantInverseImageIso f).app M
  let q : L.obj F ⟶ G := (adj.homEquiv F G).symm a
  let v := L.map b ≫ q
  have hMap : mapOfDirectImage f a 0 (Ext.mk₀ b) = Ext.mk₀ (k.inv ≫ v) := by
    change ((Ext.mk₀ k.inv).comp ((Ext.mk₀ b).mapExactFunctor L) rfl).comp
      (Ext.mk₀ q) rfl = _
    rw [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀, Category.assoc]
  have hMate : (aX.homEquiv M G) (k.inv ≫ v) = (aY.homEquiv M (R.obj G)) (b ≫ a) := by
    have h₁ : (aX.homEquiv M G) (k.inv ≫ v) = (c.homEquiv M G) v := by
      change (aX.homEquiv M G) ((aX.leftAdjointUniq c).hom.app M ≫ v) = _
      rw [aX.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app]
      exact (c.homEquiv_unit M G v).symm
    have h₂ : (c.homEquiv M G) v = (aY.homEquiv M (R.obj G)) (b ≫ a) := by
      change (aY.homEquiv M (R.obj G)) ((adj.homEquiv (Z Y) G) (L.map b ≫ q)) = _
      rw [adj.homEquiv_naturality_left]
      rw [(adj.homEquiv F G).apply_symm_apply a]
    exact h₁.trans h₂
  rw [hMap, Sheaf.H.equiv₀_naturality]
  have hExt {H₁ H₂ : C X} (g : H₁ ⟶ H₂) :
      Ext.addEquiv₀ (Ext.mk₀ g) = g := Ext.addEquiv₀.apply_symm_apply g
  have hExt' {H₁ H₂ : C Y} (g : H₁ ⟶ H₂) :
      Ext.addEquiv₀ (Ext.mk₀ g) = g := Ext.addEquiv₀.apply_symm_apply g
  simp only [Sheaf.H.equiv₀, AddEquiv.trans_apply, Sheaf.H.addEquiv₀_map, hExt, hExt']
  exact congrArg (AddCommGrpCat.uliftZMultiplesAddEquiv _) hMate

end
end ManuscriptAudit.ProetaleSchemePullbackHZero

open Lean Elab Command in
run_cmd do
  let n := ``ManuscriptAudit.ProetaleSchemePullbackHZero.equivZero_mapOfDirectImage
  let ax ← collectAxioms n
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{n} depends on unexpected axioms {ax}"
  logInfo m!"{n} uses {ax}"
