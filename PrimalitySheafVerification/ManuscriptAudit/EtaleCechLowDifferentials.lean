import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CechNerveLowDegrees
import PrimalitySheafVerification.ManuscriptAudit.EtaleCechDirectSum

/-! Positive exactness of the native Čech complex supplies actual
coboundaries on the double pullback of a covering arrow. -/

namespace ManuscriptAudit.EtaleCechLowDifferentials

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Opposite
open InjectiveCechPullback CechNerveLowDegrees EtaleCechDirectSum
open scoped Simplicial

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {C : Type*} [Category* C] [HasFiniteLimits C]
variable {U T : C} (f : U ⟶ T)
variable (P : Cᵒᵖ ⥤ AddCommGrpCat.{0})

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
  rw [restrict_restrict, restrict_restrict]
  change P.map (pair f 1 0 1 ≫ second f).op a - P.map (pair f 1 0 1 ≫ first f).op a = z
  rw [← face_zero_zero, ← face_zero_one, ← restrict_restrict, ← restrict_restrict, ha]
  exact hy'

end

end ManuscriptAudit.EtaleCechLowDifferentials

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.EtaleCechLowDifferentials.exists_boundary
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
