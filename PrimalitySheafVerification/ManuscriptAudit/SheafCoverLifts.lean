import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import PrimalitySheafVerification.ManuscriptAudit.FiniteSupportEtaleSheaf
import PrimalitySheafVerification.ManuscriptAudit.SheafH1Descent

/-!
# Lifting sections through finite covers

A locally surjective sheaf map gives lifts on a finite covering
subfamily when finite subcovers exist. Compatible lifts glue as soon as
they agree on each of the actual pairwise pullbacks.
-/

namespace ManuscriptAudit.SheafCoverLifts

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {P Q : Sheaf J AddCommGrpCat.{w}} (q : P ⟶ Q)

private theorem restrict_restrict (F : Cᵒᵖ ⥤ AddCommGrpCat.{w}) {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : F.obj (op Z)) :
    F.map f.op (F.map g.op x) = F.map (f ≫ g).op x := by
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

/-- A locally liftable section has lifts on a finite cover. -/
theorem exists_finite_cover_lifts (hFin : FiniteSupportPresheaf.HasFiniteCoverFamilies J)
    {T : C} (x : Q.obj.obj (op T)) (hLocal : Presheaf.imageSieve q.hom x ∈ J T) :
    ∃ (I : Type (max u v)) (_ : Finite I) (U : I → C) (f : ∀ i, U i ⟶ T),
      Sieve.ofArrows U f ∈ J T ∧
      ∃ y : ∀ i, P.obj.obj (op (U i)),
        ∀ i, q.hom.app (op (U i)) (y i) = Q.obj.map (f i).op x := by
  let S := Presheaf.imageSieve q.hom x
  obtain ⟨I, U, f, hS⟩ := S.exists_eq_ofArrows
  obtain ⟨t, ht⟩ := hFin U f (hS ▸ hLocal)
  have hl (i : t) : S (f i.val) := by
    rw [hS]
    exact Sieve.le_generate _ _ _ (Presieve.ofArrows.mk i.val)
  choose y hy using hl
  exact ⟨t, inferInstance, (fun i : t ↦ U i.val), (fun i : t ↦ f i.val), ht, y, hy⟩

/-- Compatible local sections glue to a lift when the cover has its
native pairwise pullbacks in the site. -/
theorem exists_lift_of_pullback_compatible [HasPullbacks C]
    [J.HasSheafCompose (forget AddCommGrpCat.{w})]
    {T : C} {I : Type*} (U : I → C) (f : ∀ i, U i ⟶ T)
    (hCover : Sieve.ofArrows U f ∈ J T)
    (x : Q.obj.obj (op T)) (y : ∀ i, P.obj.obj (op (U i)))
    (hy : ∀ i, q.hom.app (op (U i)) (y i) = Q.obj.map (f i).op x)
    (hPair : ∀ i j, P.obj.map (pullback.fst (f i) (f j)).op (y i) =
      P.obj.map (pullback.snd (f i) (f j)).op (y j)) :
    ∃ z : P.obj.obj (op T), q.hom.app (op T) z = x := by
  let Fg := forget AddCommGrpCat.{w}
  have hP : Presieve.IsSheaf J (P.obj ⋙ Fg) :=
    (isSheaf_iff_isSheaf_of_type J _).mp ((sheafCompose J Fg).obj P).property
  have hQ : Presieve.IsSheaf J (Q.obj ⋙ Fg) :=
    (isSheaf_iff_isSheaf_of_type J _).mp ((sheafCompose J Fg).obj Q).property
  have hY : Presieve.Arrows.Compatible (P.obj ⋙ Fg) f y := by
    intro i j W a b h
    let r := pullback.lift a b h
    change P.obj.map a.op (y i) = P.obj.map b.op (y j)
    calc
      _ = P.obj.map r.op (P.obj.map (pullback.fst (f i) (f j)).op (y i)) := by
        rw [restrict_restrict, pullback.lift_fst]
      _ = P.obj.map r.op (P.obj.map (pullback.snd (f i) (f j)).op (y j)) := by rw [hPair]
      _ = _ := by rw [restrict_restrict, pullback.lift_snd]
  let R := Presieve.ofArrows U f
  have hR : Sieve.generate R ∈ J T := hCover
  obtain ⟨z, hz, _⟩ := (Presieve.isSheafFor_arrows_iff (P := P.obj ⋙ Fg) (π := f)).mp
    (hP.isSheafFor R hR) y hY
  refine ⟨z, (hQ.isSheafFor R hR).isSeparatedFor.ext ?_⟩
  rintro _ _ ⟨i⟩
  change Q.obj.map (f i).op (q.hom.app (op T) z) = Q.obj.map (f i).op x
  rw [← NatTrans.naturality_apply q.hom (f i).op z]
  have hi : P.obj.map (f i).op z = y i := hz i
  rw [hi, hy]

end ManuscriptAudit.SheafCoverLifts

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.SheafCoverLifts.exists_finite_cover_lifts,
      ``ManuscriptAudit.SheafCoverLifts.exists_lift_of_pullback_compatible] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
