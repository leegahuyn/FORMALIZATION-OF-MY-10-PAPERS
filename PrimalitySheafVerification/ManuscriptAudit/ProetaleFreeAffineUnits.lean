import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleFreeExtPullback
import PrimalitySheafVerification.ManuscriptAudit.ProetaleKummerSchemePullback
import PrimalitySheafVerification.ManuscriptAudit.ProetaleCartesianChartIso

/-! Pullback at a literal affine open free representable is the specified
map on coordinate units. -/

namespace ManuscriptAudit.ProetaleFreeAffineUnits

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open ProetaleBaseChange (baseChange)
open ProetaleOpenLocalLifts (openObject)
open ProetaleMayerVietorisRepresentable (nativeFree)
open ProetaleFreeExtPullback (map map_section)
open ProetaleCartesianChartIso (chartIso)
open ProetaleKummerSchemePullback (unitsToDirectImage unitsPullback)
open EtaleProetaleFreeRepresentable (proSections proSections_natural)
open ProetaleUnitSheaf (unitSheaf specUnits)
open KummerUnitsSheaf (ringUnits)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{1}
private abbrev P (X : Scheme.{0}) := Sheaf (Scheme.ProEt.topology X) A

private def sections {X : Scheme.{0}} (U : X.ProEt) (F : P X) :
    (nativeFree U ⟶ F) ≃+ F.obj.obj (op U) where
  toEquiv := proSections X U F
  map_add' b c := by
    let t := proSections X U (nativeFree U) (𝟙 _)
    have h (g : nativeFree U ⟶ F) : proSections X U F g = g.hom.app (op U) t := by
      simpa only [Category.id_comp] using proSections_natural X U (𝟙 (nativeFree U)) g
    change proSections X U F (b + c) = proSections X U F b + proSections X U F c
    rw [h (b + c), h b, h c]
    rfl

variable {X Y : Scheme.{0}} {R S : Type} [CommRing R] [CommRing S]
  (j : Spec (CommRingCat.of R) ⟶ Y) (i : Spec (CommRingCat.of S) ⟶ X)
  [IsOpenImmersion j] [IsOpenImmersion i]

/-- Degree-zero unit classes at the actual free affine chart are coordinate units. -/
def coordinates :
    Ext (nativeFree (openObject j)) (unitSheaf Y) 0 ≃+ Additive Rˣ :=
  Ext.addEquiv₀.trans ((sections (openObject j) (unitSheaf Y)).trans
    (specUnits (CommRingCat.of R) (𝟙 (Spec (CommRingCat.of R)) ≫ j)))

variable (f : X ⟶ Y) (a : CommRingCat.of R ⟶ CommRingCat.of S)
  (H : IsPullback (Spec.map a) (openObject i).hom (openObject j).hom f)

set_option maxHeartbeats 6800000 in
/-- The affine coordinate functor records the genuine unit pullback along Spec of the ring map. -/
theorem coordinates_pullback (u : Ext (nativeFree (openObject j)) (unitSheaf Y) 0) :
    coordinates i (map f (chartIso f H) (unitsPullback f) 0 u) =
      (ringUnits.map a) (coordinates j u) := by
  obtain ⟨b, rfl⟩ := (Ext.mk₀_bijective (nativeFree (openObject j)) (unitSheaf Y)).surjective u
  let e := chartIso f H
  let V := openObject j
  let U := openObject i
  let W := (baseChange f).obj V
  let s := proSections Y V (unitSheaf Y) b
  let p : W.left ⟶ V.left := pullback.fst V.hom f
  have hFst : e.inv.left ≫ p = Spec.map a := H.isoPullback_hom_fst
  have hΓ : p.appTop ≫ e.inv.left.appTop = (Spec.map a).appTop :=
    congrArg (fun t : U.left ⟶ V.left ↦ t.appTop) hFst
  let g := unitsToDirectImage f
  have h := map_section f e g b
  have h₀ : Ext.addEquiv₀ (Ext.mk₀ b) = b := Ext.addEquiv₀.apply_symm_apply b
  have h₁ : (unitSheaf X).obj.map e.inv.op (g.hom.app (op V) s) =
      AddCommGrpCat.uliftFunctor.{1}.map (ringUnits.map (Spec.map a).appTop) s := by
    change (AddCommGrpCat.uliftFunctor.{1}.map (ringUnits.map e.inv.left.appTop))
      ((AddCommGrpCat.uliftFunctor.{1}.map (ringUnits.map p.appTop)) s) = _
    change ((AddCommGrpCat.uliftFunctor.{1}.map (ringUnits.map p.appTop)) ≫
      (AddCommGrpCat.uliftFunctor.{1}.map (ringUnits.map e.inv.left.appTop))) s = _
    rw [← Functor.map_comp, ← Functor.map_comp, hΓ]
  change specUnits _ _ (proSections X U (unitSheaf X)
      (Ext.addEquiv₀ (map f e (unitsPullback f) 0 (Ext.mk₀ b)))) =
    (ringUnits.map a) (specUnits _ _ (proSections Y V (unitSheaf Y) (Ext.addEquiv₀ (Ext.mk₀ b))))
  change proSections X U (unitSheaf X)
      (Ext.addEquiv₀ (map f e (unitsPullback f) 0 (Ext.mk₀ b))) =
    (unitSheaf X).obj.map e.inv.op (g.hom.app (op V) s) at h
  rw [h, h₀, h₁]
  have he : ringUnits.map (Spec.map a).appTop ≫ (ringUnits.mapIso
        (Scheme.ΓSpecIso (CommRingCat.of S))).hom =
      (ringUnits.mapIso (Scheme.ΓSpecIso (CommRingCat.of R))).hom ≫ ringUnits.map a := by
    simp only [Functor.mapIso_hom, ← Functor.map_comp, Scheme.ΓSpecIso_naturality]
  exact ConcreteCategory.congr_hom he s.down

end
end ManuscriptAudit.ProetaleFreeAffineUnits

open Lean Elab Command in
run_cmd do
  let n := ``ManuscriptAudit.ProetaleFreeAffineUnits.coordinates_pullback
  let ax ← collectAxioms n
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{n} depends on unexpected axioms {ax}"
  logInfo m!"{n} uses {ax}"
