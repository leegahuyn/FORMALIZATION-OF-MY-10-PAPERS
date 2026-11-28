import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleKummerSchemePullback
import PrimalitySheafVerification.ManuscriptAudit.ProetaleSchemePullbackHZero
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAffineLineCyclicHOne

/-! On the actual affine unit cohomology, scheme pullback is the ordinary
homomorphism on the coordinate ring's units. -/

namespace ManuscriptAudit.ProetaleAffineUnitPullback

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open ProetaleBaseChange (baseChange)
open ProetaleKummerSchemePullback (unitsToDirectImage unitsPullback unitsMap)
open ProetaleSchemePullbackHZero (equivZero_mapOfDirectImage)
open ProetaleSchemeCohomologyPullback (mapOfDirectImage)
open ProetaleAffineLineCyclicHOne (unitsHZeroEquiv)
open ProetaleUnitSheaf (unitSheaf specUnits)
open KummerUnitsSheaf (ringUnits)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{1}
private abbrev M := AddCommGrpCat.of (ULift.{1} ℤ)
private abbrev J (X : Scheme.{0}) := Scheme.ProEt.topology X

private theorem terminal_restrict {X : Scheme.{0}} {T T' : X.ProEt}
    (hT : IsTerminal T) (hT' : IsTerminal T') (r : T' ⟶ T)
    (F : Sheaf (J X) A) (x : Sheaf.H F 0) :
    F.obj.map r.op (Sheaf.H.equiv₀ F hT x) = Sheaf.H.equiv₀ F hT' x := by
  let v : (Functor.const X.ProEtᵒᵖ).obj M ⟶ F.obj :=
    (sheafificationAdjunction (J X) A).homEquiv _ F (Ext.addEquiv₀ x)
  have h_eval {U : X.ProEt} (hU : IsTerminal U) :
      Sheaf.H.equiv₀ F hU x = v.app (op U) ⟨1⟩ := by
    let e := constantPresheafAdj A hU
    change AddCommGrpCat.uliftZMultiplesAddEquiv _ ((e.homEquiv M F.obj) v) = _
    rw [Adjunction.homEquiv_unit]
    change ((𝟙 M) ≫ v.app (op U)) (⟨1⟩ : ULift.{1} ℤ) = _
    rw [Category.id_comp]
  rw [h_eval hT, h_eval hT']
  have h := v.naturality r.op
  change (𝟙 M) ≫ v.app (op T') = v.app (op T) ≫ F.obj.map r.op at h
  rw [Category.id_comp] at h
  exact (ConcreteCategory.congr_hom h (⟨1⟩ : ULift.{1} ℤ)).symm

variable {R S : Type} [CommRing R] [CommRing S]
  (a : CommRingCat.of R ⟶ CommRingCat.of S)

private abbrev X := Spec (CommRingCat.of S)
private abbrev Y := Spec (CommRingCat.of R)
private abbrev f := Spec.map a
private abbrev T (B : Scheme.{0}) := Scheme.ProEt.mk (𝟙 B)
private abbrev hT (B : Scheme.{0}) : IsTerminal (T B) :=
  MorphismProperty.Over.mkIdTerminal @WeaklyEtale B
private abbrev U := (baseChange (f a)).obj (T (Y (R := R)))

private def unitProjection : X (S := S) ⟶ (U a).left :=
  pullback.lift (f a) (𝟙 _) (by simp only [Category.comp_id, Category.id_comp])

private def terminalArrow : T (X (S := S)) ⟶ U a :=
  MorphismProperty.Over.homMk (unitProjection a) (pullback.lift_snd _ _ _)

set_option maxHeartbeats 6500000 in
/-- Genuine affine native degree-zero unit pullback equals the coordinate unit map. -/
theorem unitsMap_spec (u : Sheaf.H (unitSheaf (Y (R := R))) 0) :
    unitsHZeroEquiv S (unitsMap (f a) 0 u) = (ringUnits.map a) (unitsHZeroEquiv R u) := by
  let x := X (S := S)
  let y := Y (R := R)
  let g := f a
  let V := U a
  let hu : IsTerminal V := IsTerminal.isTerminalObj (baseChange g) (T y) (hT y)
  let r := terminalArrow a
  let v := Sheaf.H.equiv₀ (unitSheaf y) (hT y) u
  let b := unitsToDirectImage g
  have h₁ : Sheaf.H.equiv₀ (unitSheaf x) hu (unitsMap g 0 u) = b.hom.app (op (T y)) v := by
    change Sheaf.H.equiv₀ (unitSheaf x) hu (mapOfDirectImage g b 0 u) = _
    exact equivZero_mapOfDirectImage g b u
  have h₂ : (unitSheaf x).obj.map r.op (b.hom.app (op (T y)) v) =
      Sheaf.H.equiv₀ (unitSheaf x) (hT x) (unitsMap g 0 u) :=
    (congrArg ((unitSheaf x).obj.map r.op) h₁).symm.trans
      (terminal_restrict hu (hT x) r (unitSheaf x) _)
  change specUnits (CommRingCat.of S) (𝟙 x)
      (Sheaf.H.equiv₀ (unitSheaf x) (hT x) (unitsMap g 0 u)) =
    (ringUnits.map a) (specUnits (CommRingCat.of R) (𝟙 y) v)
  rw [← h₂]
  let p : V.left ⟶ y := pullback.fst (𝟙 y) g
  have hProj : r.left ≫ p = g := pullback.lift_fst _ _ _
  have h₃ : p.appTop ≫ r.left.appTop = g.appTop :=
    congrArg (fun t : x ⟶ y ↦ t.appTop) hProj
  have h₄ : ringUnits.map g.appTop ≫ (ringUnits.mapIso (Scheme.ΓSpecIso (CommRingCat.of S))).hom =
      (ringUnits.mapIso (Scheme.ΓSpecIso (CommRingCat.of R))).hom ≫ ringUnits.map a := by
    simp only [Functor.mapIso_hom, ← Functor.map_comp, Scheme.ΓSpecIso_naturality]
  change ((ringUnits.mapIso (Scheme.ΓSpecIso (CommRingCat.of S))).hom)
      ((ringUnits.map r.left.appTop) ((ringUnits.map p.appTop) v.down)) = _
  have h₅ : (ringUnits.map r.left.appTop) ((ringUnits.map p.appTop) v.down) =
      (ringUnits.map g.appTop) v.down := by
    change (ringUnits.map p.appTop ≫ ringUnits.map r.left.appTop) v.down = _
    rw [← Functor.map_comp, h₃]
  rw [h₅]
  exact ConcreteCategory.congr_hom h₄ v.down

end
end ManuscriptAudit.ProetaleAffineUnitPullback

open Lean Elab Command in
run_cmd do
  let n := ``ManuscriptAudit.ProetaleAffineUnitPullback.unitsMap_spec
  let ax ← collectAxioms n
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{n} depends on unexpected axioms {ax}"
  logInfo m!"{n} uses {ax}"
