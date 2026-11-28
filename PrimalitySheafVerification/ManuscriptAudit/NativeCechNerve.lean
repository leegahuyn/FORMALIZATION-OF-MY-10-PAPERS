import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.CechNerveLowDegrees
import PrimalitySheafVerification.ManuscriptAudit.SheafCechDifference
import PrimalitySheafVerification.ManuscriptAudit.SheafExplicitCechHOne

/-! Coefficient-universe-polymorphic Čech complexes and section descent
on the actual chosen site and its literal pullback nerve. -/

namespace ManuscriptAudit.NativeCechNerve

open CategoryTheory CategoryTheory.Limits Opposite
open InjectiveCechPullback CechNerveLowDegrees
open SingletonCoverRefinement (Covers)
open scoped Simplicial

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v w

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
variable {U T : C} (f : U ⟶ T)

private abbrev Ab := AddCommGrpCat.{w}

def cochains : (Cᵒᵖ ⥤ Ab.{w}) ⥤ CochainComplex Ab.{w} ℕ :=
  (CategoryTheory.Functor.whiskeringLeft _ _ _).obj (Arrow.mk f).cechNerve.rightOp ⋙
    alternatingCofaceMapComplex Ab.{w}

abbrev Cech (P : Cᵒᵖ ⥤ Ab.{w}) := (cochains f).obj P

instance : (cochains.{u,v,w} f).PreservesZeroMorphisms where
  map_zero _ _ := by
    ext n
    rfl

theorem cochainExactAt_succ_iff (K : CochainComplex Ab.{w} ℕ) (n : ℕ) :
    K.ExactAt (n + 1) ↔ ∀ z : K.X (n + 1), K.d (n + 1) (n + 2) z = 0 →
      ∃ y : K.X n, K.d n (n + 1) y = z :=
  (K.exactAt_iff' (i := n) (j := n + 1) (k := n + 2)
    (CochainComplex.prev_nat_succ n) (CochainComplex.next ℕ (n + 1))).trans
      (ShortComplex.ab_exact_iff (K.sc' n (n + 1) (n + 2)))

variable (P : Cᵒᵖ ⥤ Ab.{w})

private theorem differential (n : ℕ) :
    (Cech f P).d n (n + 1) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • P.map (face f n i).op := by
  let A := (Arrow.mk f).cechNerve.rightOp ⋙ P
  change (AlternatingCofaceMapComplex.obj A).d n (n + 1) = _
  exact CochainComplex.of_d (fun i : ℕ ↦ A.obj ⦋i⦌)
    (AlternatingCofaceMapComplex.objD A) n

private theorem d₀ (x : P.obj (op (N f 0))) :
    (Cech f P).d 0 1 x = P.map (face f 0 0).op x - P.map (face f 0 1).op x := by
  rw [differential, Fin.sum_univ_two]
  change ((1 : ℤ) • P.map (face f 0 0).op + (-1 : ℤ) • P.map (face f 0 1).op) x = _
  rw [one_zsmul, neg_smul, one_zsmul, AddCommGrpCat.hom_add_apply]
  exact (sub_eq_add_neg _ _).symm

private theorem d₁ (x : P.obj (op (N f 1))) :
    (Cech f P).d 1 2 x =
      P.map (face f 1 0).op x - P.map (face f 1 1).op x + P.map (face f 1 2).op x := by
  rw [differential, Fin.sum_univ_succ, Fin.sum_univ_two]
  change ((1 : ℤ) • P.map (face f 1 0).op +
    ((-1 : ℤ) • P.map (face f 1 1).op + (1 : ℤ) • P.map (face f 1 2).op)) x = _
  rw [one_zsmul, neg_smul, one_zsmul, one_zsmul,
    AddCommGrpCat.hom_add_apply, AddCommGrpCat.hom_add_apply]
  change P.map (face f 1 0).op x + (-P.map (face f 1 1).op x + P.map (face f 1 2).op x) = _
  abel

private theorem restrict_restrict {X Y Z : C} (a : X ⟶ Y) (b : Y ⟶ Z)
    (x : P.obj (op Z)) : P.map a.op (P.map b.op x) = P.map (a ≫ b).op x := by
  rw [op_comp, CategoryTheory.Functor.map_comp, ConcreteCategory.comp_apply]

/-- A cocycle given on the usual double and triple pullbacks has an
actual local primitive when the Čech complex is exact in degree one. -/
theorem exists_boundary (h : (Cech f P).ExactAt 1)
    (b : P.obj (op (Double f)))
    (hb : P.map (edge23 f).op b - P.map (edge13 f).op b + P.map (edge12 f).op b = 0) :
    ∃ a : P.obj (op U), b = P.map (second f).op a - P.map (first f).op a := by
  let p := pair f 1 0 1
  let z := P.map p.op b
  have hz : (Cech f P).d 1 2 z = 0 := by
    rw [d₁]
    change P.map (face f 1 0).op (P.map p.op b) -
      P.map (face f 1 1).op (P.map p.op b) + P.map (face f 1 2).op (P.map p.op b) = 0
    rw [restrict_restrict, restrict_restrict, restrict_restrict]
    change P.map (face f 1 0 ≫ pair f 1 0 1).op b -
      P.map (face f 1 1 ≫ pair f 1 0 1).op b +
      P.map (face f 1 2 ≫ pair f 1 0 1).op b = 0
    rw [face_one_zero, face_one_one, face_one_two,
      ← restrict_restrict, ← restrict_restrict, ← restrict_restrict]
    change (P.map (triple f).op).hom _ - (P.map (triple f).op).hom _ +
      (P.map (triple f).op).hom _ = 0
    rw [← map_sub, ← map_add, hb, map_zero]
  obtain ⟨y, hy⟩ := (cochainExactAt_succ_iff (Cech f P) 0).mp h z hz
  have hy' := (d₀ f P y).symm.trans hy
  let a := P.map (zeroIso f).inv.op y
  have ha : P.map (zeroIso f).hom.op a = y := by
    change P.map (zeroIso f).hom.op (P.map (zeroIso f).inv.op y) = y
    rw [restrict_restrict, (zeroIso f).hom_inv_id, op_id, CategoryTheory.Functor.map_id] <;> rfl
  have hs : Function.LeftInverse (P.map (doubleSection f).op) (P.map p.op) := by
    intro x
    rw [restrict_restrict]
    change P.map (doubleSection f ≫ pair f 1 0 1).op x = x
    rw [doubleSection_pair, op_id, CategoryTheory.Functor.map_id] <;> rfl
  refine ⟨a, hs.injective ?_⟩
  change z = (P.map p.op).hom (P.map (second f).op a - P.map (first f).op a)
  symm
  rw [map_sub]
  change P.map p.op (P.map (second f).op a) - P.map p.op (P.map (first f).op a) = z
  have hFace (s : Double f ⟶ U) (d : N f 1 ⟶ N f 0)
      (hd : d ≫ (zeroIso f).hom = p ≫ s) :
      P.map p.op (P.map s.op a) = P.map d.op y := by
    calc
      _ = P.map (p ≫ s).op a := restrict_restrict P p s a
      _ = P.map (d ≫ (zeroIso f).hom).op a :=
        congrArg (fun g : N f 1 ⟶ U ↦ P.map g.op a) hd.symm
      _ = P.map d.op (P.map (zeroIso f).hom.op a) :=
        (restrict_restrict P d (zeroIso f).hom a).symm
      _ = _ := congrArg (fun t ↦ P.map d.op t) ha
  exact (congrArg₂ (fun x₁ x₂ : P.obj (op (N f 1)) ↦ x₁ - x₂)
    (hFace (second f) (face f 0 0) (face_zero_zero f))
    (hFace (first f) (face f 0 1) (face_zero_one f))).trans hy'


variable {J : GrothendieckTopology C} [HasSheafify J Ab.{w}]
  [J.HasSheafCompose (forget Ab.{w})]
  {D I : Sheaf J Ab.{w}} (i : D ⟶ I) [Mono i]

/-- Degree-one exactness of the actual Čech nerve descends a cokernel lift. -/
theorem exists_global_lift (hf : Covers J f) (h : (Cech f D.obj).ExactAt 1)
    (x : (cokernel i).obj.obj (op T)) (y : I.obj.obj (op U))
    (hy : (cokernel.π i).hom.app (op U) y = (cokernel i).obj.map f.op x) :
    ∃ z : I.obj.obj (op T), (cokernel.π i).hom.app (op T) z = x := by
  obtain ⟨b, hb, hc⟩ := SheafCechDifference.exists_cocycle_of_local_lift i f x y hy
  obtain ⟨a, ha⟩ := exists_boundary f D.obj h b hc
  apply SheafExplicitCechHOne.exists_global_lift i f (first f) (second f)
    (IsPullback.of_hasPullback f f) hf x y hy a
  rw [← ha]
  exact hb

end
end ManuscriptAudit.NativeCechNerve

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NativeCechNerve.cochainExactAt_succ_iff,
      ``ManuscriptAudit.NativeCechNerve.exists_boundary,
      ``ManuscriptAudit.NativeCechNerve.exists_global_lift] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
