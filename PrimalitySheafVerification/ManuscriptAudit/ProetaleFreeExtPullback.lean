import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleSchemeFreeSquarePullback

/-! Cohomological pullback with a native free chart as its representing
source agrees in degree zero with the actual base-changed sections. -/

namespace ManuscriptAudit.ProetaleFreeExtPullback

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open ProetaleBaseChange (baseChange directImage)
open ProetaleInverseImage (inverseImage adjunction)
open ProetaleMayerVietorisRepresentable (nativeFree)
open ProetaleSchemeFreeRepresentable (inverseImageIso sectionComparison
  sectionComparison_natural comparison_hom)
open ProetaleSchemeFreeSquarePullback (free)
open EtaleProetaleFreeRepresentable (proSections proSections_freeMap)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{1}
private abbrev P (X : Scheme.{0}) := Sheaf (Scheme.ProEt.topology X) A

variable {X Y : Scheme.{0}} (f : X ⟶ Y) {U : X.ProEt} {V : Y.ProEt}
  (e : (baseChange f).obj V ≅ U)

abbrev chartIso : (inverseImage f).obj (nativeFree V) ≅ nativeFree U :=
  inverseImageIso f V ≪≫ (free X).mapIso e

/-- Pullback on the actual Ext group at the specified pro-étale chart. -/
def map {F : P Y} {G : P X} (a : (inverseImage f).obj F ⟶ G) (n : ℕ) :
    Ext (nativeFree V) F n →+ Ext (nativeFree U) G n :=
  ((Ext.mk₀ a).postcomp (nativeFree U) (add_zero n)).comp
    (((Ext.mk₀ (chartIso f e).inv).precomp ((inverseImage f).obj F) (zero_add n)).comp
      ((inverseImage f).mapExtAddHom (nativeFree V) F n))

theorem map_mk {F : P Y} {G : P X} (a : (inverseImage f).obj F ⟶ G)
    (b : nativeFree V ⟶ F) :
    map f e a 0 (Ext.mk₀ b) = Ext.mk₀ ((chartIso f e).inv ≫ (inverseImage f).map b ≫ a) := by
  change ((Ext.mk₀ (chartIso f e).inv).comp
      ((Ext.mk₀ b).mapExactFunctor (inverseImage f)) rfl).comp (Ext.mk₀ a) rfl = _
  rw [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀, Category.assoc]

private theorem map_hom_sections {F : P Y} {G : P X}
    (a : F ⟶ (directImage f A).obj G) (b : nativeFree V ⟶ F) :
    proSections X ((baseChange f).obj V) G
      ((inverseImageIso f V).inv ≫ (inverseImage f).map b ≫ ((adjunction f).homEquiv F G).symm a) =
      a.hom.app (op V) (proSections Y V F b) := by
  let i := inverseImageIso f V
  let adj := adjunction f
  let q := (adj.homEquiv F G).symm a
  let v := (inverseImage f).map b ≫ q
  have h := sectionComparison_natural f V i.hom (i.inv ≫ v)
  rw [comparison_hom, Category.id_comp, ← Category.assoc, i.hom_inv_id, Category.id_comp] at h
  change proSections X ((baseChange f).obj V) G (i.inv ≫ v) = _
  refine (congrArg (proSections X ((baseChange f).obj V) G) h.symm).trans ?_
  change proSections X ((baseChange f).obj V) G
    ((proSections X ((baseChange f).obj V) G).symm
      (proSections Y V ((directImage f A).obj G) ((adj.homEquiv _ _) v))) = _
  rw [Equiv.apply_symm_apply]
  change proSections Y V ((directImage f A).obj G)
    ((adj.homEquiv _ _) ((inverseImage f).map b ≫ q)) = _
  rw [adj.homEquiv_naturality_left]
  rw [show (adj.homEquiv F G) q = a from (adj.homEquiv F G).apply_symm_apply a]
  exact EtaleProetaleFreeRepresentable.proSections_natural Y V b a

/-- Pullback evaluates as the literal restriction of the coefficient map on sections. -/
theorem map_section {F : P Y} {G : P X} (a : F ⟶ (directImage f A).obj G)
    (b : nativeFree V ⟶ F) :
    proSections X U G (Ext.addEquiv₀ (map f e (((adjunction f).homEquiv F G).symm a) 0
      (Ext.mk₀ b))) =
      G.obj.map e.inv.op (a.hom.app (op V) (proSections Y V F b)) := by
  rw [map_mk]
  let h : nativeFree U ⟶ G := (chartIso f e).inv ≫
    (inverseImage f).map b ≫ ((adjunction f).homEquiv F G).symm a
  have hh : Ext.addEquiv₀ (Ext.mk₀ h) = h := Ext.addEquiv₀.apply_symm_apply h
  change proSections X U G (Ext.addEquiv₀ (Ext.mk₀ h)) = _
  rw [hh]
  change proSections X U G
    (((free X).map e.inv ≫ (inverseImageIso f V).inv) ≫
      (inverseImage f).map b ≫ ((adjunction f).homEquiv F G).symm a) = _
  rw [Category.assoc]
  change proSections X U G (EtaleProetaleFreeRepresentable.proFreeMap X e.inv ≫ _) = _
  rw [proSections_freeMap, map_hom_sections]

set_option maxHeartbeats 5200000 in
/-- A native exact chart pullback commutes with the actual covariant boundary. -/
theorem map_boundary {S : ShortComplex (P Y)} {T : ShortComplex (P X)}
    (hS : S.ShortExact) (hT : T.ShortExact) (a : S.map (inverseImage f) ⟶ T)
    (n : ℕ) (u : Ext (nativeFree V) S.X₃ n) :
    map f e a.τ₁ (n + 1) (u.comp hS.extClass rfl) =
      (map f e a.τ₃ n u).comp hT.extClass rfl := by
  let L := inverseImage f
  let hL := hS.map_of_exact L
  let p := Ext.mk₀ (chartIso f e).inv
  let v := u.mapExactFunctor L
  have w := hL.extClass_naturality hT a
  change hL.extClass.comp (Ext.mk₀ a.τ₁) rfl =
    (Ext.mk₀ a.τ₃).comp hT.extClass rfl at w
  change (p.comp ((u.comp hS.extClass rfl).mapExactFunctor L) (zero_add (n + 1))).comp
    (Ext.mk₀ a.τ₁) (add_zero (n + 1)) =
    ((p.comp v (zero_add n)).comp (Ext.mk₀ a.τ₃) (add_zero n)).comp hT.extClass rfl
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
  change (p.comp (v.comp hL.extClass rfl) (zero_add (n + 1))).comp
    (Ext.mk₀ a.τ₁) (add_zero (n + 1)) = _
  simp only [Ext.comp_assoc_of_third_deg_zero]
  rw [w, Ext.comp_assoc, Ext.comp_assoc_of_second_deg_zero]

end
end ManuscriptAudit.ProetaleFreeExtPullback

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``ManuscriptAudit.ProetaleFreeExtPullback.map_section,
      ``ManuscriptAudit.ProetaleFreeExtPullback.map_boundary] do
    let ax ← collectAxioms n
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{n} depends on unexpected axioms {ax}"
    logInfo m!"{n} uses {ax}"
