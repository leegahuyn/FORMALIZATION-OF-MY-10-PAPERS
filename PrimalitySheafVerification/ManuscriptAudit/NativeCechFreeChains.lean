import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import PrimalitySheafVerification.ManuscriptAudit.NativeCechPointwiseCone

/-! The free representable chains of the actual Čech nerve are exact
objectwise in all positive degrees, for any arrow and any base. -/

namespace ManuscriptAudit.NativeCechFreeChains

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Opposite
open CechNerveLowDegrees (N face)
open NativeCechPointwiseCone (prepend prepend_face_zero prepend_face_succ)
open scoped Simplicial BigOperators

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v w

variable {C : Type u} [Category.{v} C]

private abbrev G := AddCommGrpCat.{max v w}

/-- The free abelian presheaf represented by an actual site object. -/
def freeYoneda : C ⥤ (Cᵒᵖ ⥤ G.{v,w}) :=
  yoneda ⋙ (CategoryTheory.Functor.whiskeringRight _ _ _).obj
    (CategoryTheory.uliftFunctor.{w} ⋙ AddCommGrpCat.free)

/-- Evaluation of a morphism between abelian groups at an element is additive. -/
def evaluateHom {V W : G.{v,w}} (x : V) : (V ⟶ W) →+ W where
  toFun f := f x
  map_zero' := rfl
  map_add' _ _ := rfl

theorem freeYoneda_map_of {X Y W : C} (f : X ⟶ Y) (a : W ⟶ X) :
    ((freeYoneda.{u,v,w}).map f).app (op W) (FreeAbelianGroup.of (ULift.up a)) =
      FreeAbelianGroup.of (ULift.up (a ≫ f)) :=
  FreeAbelianGroup.map_of_apply _

variable [HasFiniteLimits C] {U T : C} (f : U ⟶ T)

private abbrev S := (Arrow.mk f).cechNerve ⋙ freeYoneda.{u,v,w}

/-- The literal alternating boundary of the actual representable Čech nerve. -/
abbrev boundary (n : ℕ) :
    (freeYoneda.{u,v,w}).obj (N f (n + 1)) ⟶ (freeYoneda.{u,v,w}).obj (N f n) :=
  AlternatingFaceMapComplex.objD (S.{u,v,w} f) n

theorem boundary_formula (n : ℕ) :
    boundary.{u,v,w} f n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (freeYoneda.{u,v,w}).map (face f n i) :=
  rfl

theorem boundary_squared (n : ℕ) : boundary.{u,v,w} f (n + 1) ≫ boundary f n = 0 :=
  AlternatingFaceMapComplex.d_squared (S.{u,v,w} f) n

private theorem boundary_of {W : C} (n : ℕ) (a : W ⟶ N f (n + 1)) :
    (boundary.{u,v,w} f n).app (op W) (FreeAbelianGroup.of (ULift.up a)) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        (FreeAbelianGroup.of (ULift.up (a ≫ face f n i))) := by
  rw [boundary_formula, NatTrans.app_sum]
  let ev := evaluateHom (V := ((freeYoneda.{u,v,w}).obj (N f (n + 1))).obj (op W))
    (W := ((freeYoneda.{u,v,w}).obj (N f n)).obj (op W)) (FreeAbelianGroup.of (ULift.up a))
  change ev (∑ i, _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [NatTrans.app_zsmul, map_zsmul]
  change _ • ((freeYoneda.{u,v,w}).map (face f n i)).app (op W)
    (FreeAbelianGroup.of (ULift.up a)) = _
  rw [freeYoneda_map_of]

private def cone (W : C) (n : ℕ) :
    ((freeYoneda.{u,v,w}).obj (N f n)).obj (op W) →+
      ((freeYoneda.{u,v,w}).obj (N f (n + 1))).obj (op W) :=
  FreeAbelianGroup.map (fun a ↦ ULift.up (prepend f n a.down))

private theorem cone_of {W : C} (n : ℕ) (a : W ⟶ N f n) :
    cone.{u,v,w} f W n (FreeAbelianGroup.of (ULift.up a)) =
      FreeAbelianGroup.of (ULift.up (prepend f n a)) :=
  FreeAbelianGroup.map_of_apply _

set_option maxHeartbeats 3900000 in
private theorem cone_identity (W : C) (n : ℕ) :
    ((boundary.{u,v,w} f (n + 1)).app (op W)).hom.comp (cone.{u,v,w} f W (n + 1)) +
      (cone.{u,v,w} f W n).comp ((boundary.{u,v,w} f n).app (op W)).hom =
        AddMonoidHom.id (((freeYoneda.{u,v,w}).obj (N f (n + 1))).obj (op W)) := by
  apply FreeAbelianGroup.lift_ext
  rintro ⟨a⟩
  change W ⟶ N f (n + 1) at a
  change (boundary.{u,v,w} f (n + 1)).app (op W)
      (cone.{u,v,w} f W (n + 1) (FreeAbelianGroup.of (ULift.up a))) +
    cone.{u,v,w} f W n ((boundary.{u,v,w} f n).app (op W) (FreeAbelianGroup.of (ULift.up a))) =
      FreeAbelianGroup.of (ULift.up a)
  rw [cone_of, boundary_of, boundary_of, map_sum]
  have h (i : Fin (n + 2)) :
      cone.{u,v,w} f W n ((-1 : ℤ) ^ (i : ℕ) •
        FreeAbelianGroup.of (ULift.up (a ≫ face f n i))) =
      (-1 : ℤ) ^ (i : ℕ) • FreeAbelianGroup.of (ULift.up (prepend f n (a ≫ face f n i))) := by
    rw [map_zsmul, cone_of]
  simp only [h]
  have hSign (i : Fin (n + 2)) : (-1 : ℤ) ^ (i.succ : ℕ) = -((-1 : ℤ) ^ (i : ℕ)) := by
    rw [Fin.val_succ, pow_succ, mul_neg, mul_one]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_zsmul, prepend_face_zero, hSign, neg_zsmul,
    prepend_face_succ]
  rw [Finset.sum_neg_distrib, add_assoc, neg_add_cancel, add_zero]

/-- A cycle in any positive degree of the actual free Čech nerve
is the boundary of its objectwise prepended chain. -/
theorem exists_boundary_of_cycle (W : C) (n : ℕ)
    (z : ((freeYoneda.{u,v,w}).obj (N f (n + 1))).obj (op W))
    (hz : (boundary.{u,v,w} f n).app (op W) z = 0) :
    ∃ x : ((freeYoneda.{u,v,w}).obj (N f (n + 2))).obj (op W),
      (boundary.{u,v,w} f (n + 1)).app (op W) x = z := by
  refine ⟨cone.{u,v,w} f W (n + 1) z, ?_⟩
  have h := DFunLike.congr_fun (cone_identity.{u,v,w} f W n) z
  change (boundary.{u,v,w} f (n + 1)).app (op W) (cone.{u,v,w} f W (n + 1) z) +
    cone.{u,v,w} f W n ((boundary.{u,v,w} f n).app (op W) z) = z at h
  simpa only [hz, map_zero, add_zero] using h

end
end ManuscriptAudit.NativeCechFreeChains

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NativeCechFreeChains.exists_boundary_of_cycle
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
