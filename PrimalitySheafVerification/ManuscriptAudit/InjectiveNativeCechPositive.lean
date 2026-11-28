import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Sites.Abelian
import PrimalitySheafVerification.ManuscriptAudit.NativeCechFreeChains
import PrimalitySheafVerification.ManuscriptAudit.NativeCechNerve

/-! Injective actual sheaves have exact positive-degree Čech
cochains on every literal singleton nerve, including affine covers
of nonterminal objects. -/

namespace ManuscriptAudit.InjectiveNativeCechPositive

open CategoryTheory CategoryTheory.Limits Opposite
open CechNerveLowDegrees (N face)
open NativeCechFreeChains (freeYoneda boundary boundary_formula boundary_squared evaluateHom)
open NativeCechNerve (Cech cochainExactAt_succ_iff)
open scoped BigOperators Simplicial

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v w

variable {C : Type u} [Category.{v} C]

private abbrev G := AddCommGrpCat.{max v w}

private def eval (X : C) (P : Cᵒᵖ ⥤ G.{v,w}) :
    ((freeYoneda.{u,v,w}).obj X ⟶ P) →+ P.obj (op X) where
  toFun p := p.app (op X) (FreeAbelianGroup.of (ULift.up (𝟙 X)))
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem eval_on_generator {X W : C} {P : Cᵒᵖ ⥤ G.{v,w}}
    (p : (freeYoneda.{u,v,w}).obj X ⟶ P) (a : W ⟶ X) :
    p.app (op W) (FreeAbelianGroup.of (ULift.up a)) =
      P.map a.op (eval.{u,v,w} X P p) := by
  have h := congrArg (fun m : ((freeYoneda.{u,v,w}).obj X).obj (op X) ⟶ P.obj (op W) ↦
    m (FreeAbelianGroup.of (ULift.up (𝟙 X)))) (p.naturality a.op)
  change p.app (op W)
      (FreeAbelianGroup.map (fun z : ULift.{w} (X ⟶ X) ↦ ULift.up (a ≫ z.down))
        (FreeAbelianGroup.of (ULift.up (𝟙 X)))) =
      P.map a.op (eval.{u,v,w} X P p) at h
  rw [FreeAbelianGroup.map_of_apply, Category.comp_id] at h
  exact h

private theorem eval_injective (X : C) (P : Cᵒᵖ ⥤ G.{v,w}) :
    Function.Injective (eval.{u,v,w} X P) := by
  intro p q h
  ext1
  funext W
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  rintro ⟨a⟩
  change p.app (op W.unop) (FreeAbelianGroup.of (ULift.up a)) =
    q.app (op W.unop) (FreeAbelianGroup.of (ULift.up a))
  rw [eval_on_generator, eval_on_generator, h]

private def fromElement (X : C) (P : Cᵒᵖ ⥤ G.{v,w}) (x : P.obj (op X)) :
    (freeYoneda.{u,v,w}).obj X ⟶ P where
  app W := AddCommGrpCat.ofHom (FreeAbelianGroup.lift
    (fun a : ULift.{w} (W.unop ⟶ X) ↦ P.map a.down.op x))
  naturality {W V} r := by
    apply AddCommGrpCat.hom_ext
    apply FreeAbelianGroup.lift_ext
    rintro ⟨a⟩
    change
      FreeAbelianGroup.lift (fun b : ULift.{w} (V.unop ⟶ X) ↦ P.map b.down.op x)
        (FreeAbelianGroup.map (fun b : ULift.{w} (W.unop ⟶ X) ↦ ULift.up (r.unop ≫ b.down))
          (FreeAbelianGroup.of (ULift.up a))) =
      P.map r (FreeAbelianGroup.lift (fun b : ULift.{w} (W.unop ⟶ X) ↦ P.map b.down.op x)
        (FreeAbelianGroup.of (ULift.up a)))
    rw [FreeAbelianGroup.map_of_apply, FreeAbelianGroup.lift_apply_of,
      FreeAbelianGroup.lift_apply_of]
    change P.map (r.unop ≫ a).op x = P.map r (P.map a.op x)
    rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply] <;> rfl

private theorem eval_fromElement (X : C) (P : Cᵒᵖ ⥤ G.{v,w}) (x : P.obj (op X)) :
    eval.{u,v,w} X P (fromElement X P x) = x := by
  change FreeAbelianGroup.lift (fun a : ULift.{w} (X ⟶ X) ↦ P.map a.down.op x)
    (FreeAbelianGroup.of (ULift.up (𝟙 X))) = x
  rw [FreeAbelianGroup.lift_apply_of]
  change P.map (𝟙 X).op x = x
  rw [op_id, Functor.map_id] <;> rfl

private theorem eval_precompose {X Y : C} (g : X ⟶ Y) {P : Cᵒᵖ ⥤ G.{v,w}}
    (m : (freeYoneda.{u,v,w}).obj Y ⟶ P) :
    eval.{u,v,w} X P ((freeYoneda.{u,v,w}).map g ≫ m) =
      P.map g.op (eval.{u,v,w} Y P m) := by
  change m.app (op X) (((freeYoneda.{u,v,w}).map g).app (op X)
    (FreeAbelianGroup.of (ULift.up (𝟙 X)))) = _
  rw [NativeCechFreeChains.freeYoneda_map_of, Category.id_comp]
  exact eval_on_generator m g

variable [HasFiniteLimits C] {U T : C} (f : U ⟶ T)

private theorem differential (P : Cᵒᵖ ⥤ G.{v,w}) (n : ℕ) :
    (Cech f P).d n (n + 1) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • P.map (face f n i).op := by
  let A := (Arrow.mk f).cechNerve.rightOp ⋙ P
  change (AlternatingCofaceMapComplex.obj A).d n (n + 1) = _
  exact CochainComplex.of_d (fun i : ℕ ↦ A.obj ⦋i⦌)
    (AlternatingCofaceMapComplex.objD A) n

private theorem eval_boundary (P : Cᵒᵖ ⥤ G.{v,w}) (n : ℕ)
    (m : (freeYoneda.{u,v,w}).obj (N f n) ⟶ P) :
    eval.{u,v,w} (N f (n + 1)) P (boundary.{u,v,w} f n ≫ m) =
      (Cech f P).d n (n + 1) (eval.{u,v,w} (N f n) P m) := by
  rw [boundary_formula, Preadditive.sum_comp, differential]
  simp only [Preadditive.zsmul_comp, map_sum, map_zsmul, eval_precompose]
  change _ = evaluateHom (eval.{u,v,w} (N f n) P m) (∑ i, _)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul] <;> rfl

private def exactShortComplex (n : ℕ) : ShortComplex (Cᵒᵖ ⥤ G.{v,w}) :=
  ShortComplex.mk (boundary.{u,v,w} f (n + 1)) (boundary f n) (boundary_squared f n)

set_option maxHeartbeats 3400000 in
private theorem shortComplex_exact (n : ℕ) : (exactShortComplex.{u,v,w} f n).Exact := by
  let S := exactShortComplex.{u,v,w} f n
  change S.Exact
  rw [S.exact_iff_kernel_ι_comp_cokernel_π_zero]
  ext1
  funext W
  let E := (CategoryTheory.evaluation Cᵒᵖ G.{v,w}).obj W
  have hE : (S.map E).Exact := by
    rw [(S.map E).ab_exact_iff]
    exact NativeCechFreeChains.exists_boundary_of_cycle.{u,v,w} f W.unop n
  have hZ : kernel.ι (E.map S.g) ≫ cokernel.π (E.map S.f) = 0 :=
    (S.map E).exact_iff_kernel_ι_comp_cokernel_π_zero.mp hE
  change E.map (kernel.ι S.g) ≫ E.map (cokernel.π S.f) = 0
  rw [← kernelComparison_comp_ι S.g E, ← π_comp_cokernelComparison S.f E,
    Category.assoc, ← Category.assoc (kernel.ι (E.map S.g)), hZ, zero_comp, comp_zero]

variable {J : GrothendieckTopology C} [HasSheafify J G.{v,w}]
  (I : Sheaf J G.{v,w}) [Injective I]

set_option maxHeartbeats 5300000 in
/-- For every actual arrow and every positive degree, the literal
Čech cochains on an injective actual sheaf are exact. -/
theorem exactAt_succ (n : ℕ) : (Cech f I.obj).ExactAt (n + 1) := by
  apply (cochainExactAt_succ_iff _ n).mpr
  intro z hz
  change I.obj.obj (op (N f (n + 1))) at z
  let p := fromElement (N f (n + 1)) I.obj z
  have hp : boundary.{u,v,w} f (n + 1) ≫ p = 0 := by
    apply eval_injective (N f (n + 2)) I.obj
    rw [eval_boundary, map_zero, eval_fromElement]
    exact hz
  let k := cokernel.desc (boundary.{u,v,w} f (n + 1))
    (boundary f n) (boundary_squared f n)
  letI : Mono k := (exactShortComplex.{u,v,w} f n).exact_iff_mono_cokernel_desc.mp
    (shortComplex_exact f n)
  let pbar := cokernel.desc (boundary.{u,v,w} f (n + 1)) p hp
  let adj := sheafificationAdjunction J G.{v,w}
  let pb := (adj.homEquiv _ I).symm pbar
  letI : Mono ((presheafToSheaf J G.{v,w}).map k) := inferInstance
  obtain ⟨qSheaf, hqSheaf⟩ := Injective.factors pb ((presheafToSheaf J G.{v,w}).map k)
  let q := adj.homEquiv _ I qSheaf
  have hq : k ≫ q = pbar := by
    rw [← adj.homEquiv_naturality_left, hqSheaf]
    exact (adj.homEquiv _ I).apply_symm_apply pbar
  have hfac : boundary.{u,v,w} f n ≫ q = p := by
    calc
      _ = cokernel.π (boundary.{u,v,w} f (n + 1)) ≫ k ≫ q := by
        rw [← Category.assoc, cokernel.π_desc]
      _ = _ := by rw [hq]; exact cokernel.π_desc _ _ _
  refine ⟨eval (N f n) I.obj q, ?_⟩
  have he := congrArg (eval.{u,v,w} (N f (n + 1)) I.obj) hfac
  rw [eval_boundary, eval_fromElement] at he
  exact he

end
end ManuscriptAudit.InjectiveNativeCechPositive

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.InjectiveNativeCechPositive.exactAt_succ
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
