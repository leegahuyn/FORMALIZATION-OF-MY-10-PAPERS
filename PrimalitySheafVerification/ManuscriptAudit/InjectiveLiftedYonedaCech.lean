import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Sites.Abelian
import PrimalitySheafVerification.ManuscriptAudit.FreeAbelianPairBoundary

/-! The injective Čech argument works when the coefficient universe is
larger than the morphism universe of the actual site. -/

namespace ManuscriptAudit.InjectiveLiftedYonedaCech

open CategoryTheory CategoryTheory.Limits Opposite
open FreeAbelianGroup FreeAbelianPairBoundary

universe u v w

variable {C : Type u} [Category.{v} C]

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev H (U : C) (W : Cᵒᵖ) := ULift.{w} (W.unop ⟶ U)
private abbrev A := AddCommGrpCat.{max v w}

private def pre {U : C} {W V : Cᵒᵖ} (f : W ⟶ V) (a : H.{u,v,w} U W) : H.{u,v,w} U V :=
  ⟨f.unop ≫ a.down⟩

private def pairTypes (U : C) : Cᵒᵖ ⥤ Type (max v w) where
  obj W := H.{u,v,w} U W × H.{u,v,w} U W
  map f := TypeCat.ofHom (fun p ↦ (pre f p.1, pre f p.2))
  map_id W := by
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨a⟩,⟨b⟩⟩
    change (ULift.up (𝟙 _ ≫ a), ULift.up (𝟙 _ ≫ b)) = (ULift.up a, ULift.up b)
    simp
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨a⟩,⟨b⟩⟩
    change (ULift.up ((g.unop ≫ f.unop) ≫ a), ULift.up ((g.unop ≫ f.unop) ≫ b)) =
      (ULift.up (g.unop ≫ f.unop ≫ a), ULift.up (g.unop ≫ f.unop ≫ b))
    simp only [Category.assoc]

private def tripleTypes (U : C) : Cᵒᵖ ⥤ Type (max v w) where
  obj W := H.{u,v,w} U W × H.{u,v,w} U W × H.{u,v,w} U W
  map f := TypeCat.ofHom (fun p ↦ (pre f p.1, pre f p.2.1, pre f p.2.2))
  map_id W := by
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨a⟩,⟨b⟩,⟨c⟩⟩
    change (ULift.up (𝟙 _ ≫ a), ULift.up (𝟙 _ ≫ b), ULift.up (𝟙 _ ≫ c)) =
      (ULift.up a, ULift.up b, ULift.up c)
    simp
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨a⟩,⟨b⟩,⟨c⟩⟩
    change (ULift.up ((g.unop ≫ f.unop) ≫ a), ULift.up ((g.unop ≫ f.unop) ≫ b),
      ULift.up ((g.unop ≫ f.unop) ≫ c)) =
      (ULift.up (g.unop ≫ f.unop ≫ a), ULift.up (g.unop ≫ f.unop ≫ b),
        ULift.up (g.unop ≫ f.unop ≫ c))
    simp only [Category.assoc]

private abbrev singles (U : C) : Cᵒᵖ ⥤ A.{v,w} :=
  yoneda.obj U ⋙ CategoryTheory.uliftFunctor.{w} ⋙ AddCommGrpCat.free

private abbrev pairs (U : C) : Cᵒᵖ ⥤ A.{v,w} :=
  pairTypes.{u,v,w} U ⋙ AddCommGrpCat.free

private abbrev triples (U : C) : Cᵒᵖ ⥤ A.{v,w} :=
  tripleTypes.{u,v,w} U ⋙ AddCommGrpCat.free

private def dOne (U : C) : pairs.{u,v,w} U ⟶ singles.{u,v,w} U where
  app W := AddCommGrpCat.ofHom (pairBoundary (H.{u,v,w} U W))
  naturality {W V} f := by
    apply AddCommGrpCat.hom_ext
    change (pairBoundary _).comp (FreeAbelianGroup.map (fun p ↦ (pre f p.1, pre f p.2))) =
      (FreeAbelianGroup.map (pre f)).comp (pairBoundary _)
    apply lift_ext
    rintro ⟨a, b⟩
    simp only [AddMonoidHom.comp_apply, map_of_apply, pairBoundary_of, map_sub]

private def dTwo (U : C) : triples.{u,v,w} U ⟶ pairs.{u,v,w} U where
  app W := AddCommGrpCat.ofHom (tripleBoundary (H.{u,v,w} U W))
  naturality {W V} f := by
    apply AddCommGrpCat.hom_ext
    change (tripleBoundary _).comp (FreeAbelianGroup.map (fun p ↦
        (pre f p.1, pre f p.2.1, pre f p.2.2))) =
      (FreeAbelianGroup.map (fun p ↦ (pre f p.1, pre f p.2))).comp (tripleBoundary _)
    apply lift_ext
    rintro ⟨a, b, c⟩
    simp only [AddMonoidHom.comp_apply, map_of_apply, tripleBoundary_of, map_sub, map_add]

private theorem dTwo_dOne (U : C) : dTwo.{u,v,w} U ≫ dOne.{u,v,w} U = 0 := by
  ext1
  funext W
  apply AddCommGrpCat.hom_ext
  exact pairBoundary_comp_tripleBoundary (H.{u,v,w} U W)

private def complex (U : C) : ShortComplex (Cᵒᵖ ⥤ A.{v,w}) :=
  ShortComplex.mk (dTwo U) (dOne U) (dTwo_dOne U)

private theorem complex_exact (U : C) : (complex.{u,v,w} U).Exact := by
  let S := complex.{u,v,w} U
  change S.Exact
  rw [S.exact_iff_kernel_ι_comp_cokernel_π_zero]
  ext1
  funext W
  let E := (CategoryTheory.evaluation Cᵒᵖ A.{v,w}).obj W
  have hE : (S.map E).Exact := by
    rw [(S.map E).ab_exact_iff]
    exact exists_tripleBoundary_of_pairBoundary_eq_zero (H.{u,v,w} U W)
  have hZ : kernel.ι (E.map S.g) ≫ cokernel.π (E.map S.f) = 0 :=
    (S.map E).exact_iff_kernel_ι_comp_cokernel_π_zero.mp hE
  change E.map (kernel.ι S.g) ≫ E.map (cokernel.π S.f) = 0
  rw [← kernelComparison_comp_ι S.g E, ← π_comp_cokernelComparison S.f E,
    Category.assoc, ← Category.assoc (kernel.ι (E.map S.g)), hZ, zero_comp, comp_zero]

variable (J : GrothendieckTopology C) [HasSheafify J A.{v,w}]

/-- A cocycle natural over actual pairs is a coboundary in an injective sheaf. -/
theorem exists_coboundary (U : C) (I : Sheaf J A.{v,w}) [Injective I]
    (c : ∀ {W : C}, (W ⟶ U) → (W ⟶ U) → I.obj.obj (op W))
    (hnat : ∀ {W V : C} (r : V ⟶ W) (a b : W ⟶ U),
      I.obj.map r.op (c a b) = c (r ≫ a) (r ≫ b))
    (hc : ∀ {W : C} (a b d : W ⟶ U), c b d - c a d + c a b = 0) :
    ∃ b : I.obj.obj (op U), ∀ {W : C} (a d : W ⟶ U),
      c a d = I.obj.map d.op b - I.obj.map a.op b := by
  let z : pairs.{u,v,w} U ⟶ I.obj :=
    { app := fun W ↦ AddCommGrpCat.ofHom (lift fun p ↦ c p.1.down p.2.down)
      naturality := by
        intro W V f
        apply AddCommGrpCat.hom_ext
        change (lift (fun p : H.{u,v,w} U V × H.{u,v,w} U V ↦ c p.1.down p.2.down)).comp
          (FreeAbelianGroup.map (fun p : H.{u,v,w} U W × H.{u,v,w} U W ↦ (pre f p.1, pre f p.2))) =
          (I.obj.map f).hom.comp
            (lift (fun p : H.{u,v,w} U W × H.{u,v,w} U W ↦ c p.1.down p.2.down))
        apply lift_ext
        rintro ⟨⟨a⟩,⟨b⟩⟩
        rw [AddMonoidHom.comp_apply, map_of_apply, lift_apply_of,
          AddMonoidHom.comp_apply, lift_apply_of]
        exact (hnat f.unop a b).symm }
  have hz : dTwo.{u,v,w} U ≫ z = 0 := by
    ext1
    funext W
    apply AddCommGrpCat.hom_ext
    let m : FreeAbelianGroup (H.{u,v,w} U W × H.{u,v,w} U W) →+ I.obj.obj W :=
      lift (fun p ↦ c p.1.down p.2.down)
    change m.comp (tripleBoundary _) = 0
    apply lift_ext
    rintro ⟨⟨a⟩,⟨b⟩,⟨e⟩⟩
    rw [AddMonoidHom.comp_apply, tripleBoundary_of, m.map_add, m.map_sub]
    simpa only [m, lift_apply_of, AddMonoidHom.zero_apply] using hc a b e
  let k := cokernel.desc (dTwo.{u,v,w} U) (dOne.{u,v,w} U) (dTwo_dOne U)
  letI : Mono k := (complex.{u,v,w} U).exact_iff_mono_cokernel_desc.mp (complex_exact U)
  let zbar := cokernel.desc (dTwo.{u,v,w} U) z hz
  let adj := sheafificationAdjunction J A.{v,w}
  let zb := (adj.homEquiv _ I).symm zbar
  letI : Mono ((presheafToSheaf J A.{v,w}).map k) := inferInstance
  obtain ⟨bSheaf, hbSheaf⟩ := Injective.factors zb ((presheafToSheaf J A.{v,w}).map k)
  let bPresheaf := adj.homEquiv _ I bSheaf
  have hb : k ≫ bPresheaf = zbar := by
    rw [← adj.homEquiv_naturality_left, hbSheaf]
    exact (adj.homEquiv _ I).apply_symm_apply zbar
  have hfac : dOne.{u,v,w} U ≫ bPresheaf = z := by
    calc
      _ = cokernel.π (dTwo.{u,v,w} U) ≫ k ≫ bPresheaf := by
        rw [← Category.assoc, cokernel.π_desc]
      _ = _ := by rw [hb]; exact cokernel.π_desc _ _ _
  let b := (bPresheaf.app (op U)).hom (of (ULift.up (𝟙 U)))
  refine ⟨b, ?_⟩
  intro W a e
  have hmap (r : W ⟶ U) :
      I.obj.map r.op b = (bPresheaf.app (op W)).hom (of (ULift.up r)) := by
    have h := congrArg (fun m : (singles.{u,v,w} U).obj (op U) ⟶ I.obj.obj (op W) ↦
      m.hom (of (ULift.up (𝟙 U)))) (bPresheaf.naturality r.op)
    change (bPresheaf.app (op W)).hom
        (FreeAbelianGroup.map (pre r.op) (of (ULift.up (𝟙 U)))) = I.obj.map r.op b at h
    simpa only [pre, map_of_apply, Category.comp_id] using h.symm
  have h := congrArg (fun m : pairs.{u,v,w} U ⟶ I.obj ↦
    (m.app (op W)).hom (of (ULift.up a, ULift.up e))) hfac
  let bMap : FreeAbelianGroup (H.{u,v,w} U (op W)) →+ I.obj.obj (op W) :=
    (bPresheaf.app (op W)).hom
  change bMap (pairBoundary _ (of (ULift.up a, ULift.up e))) =
    lift (fun p : H.{u,v,w} U (op W) × H.{u,v,w} U (op W) ↦ c p.1.down p.2.down)
      (of (ULift.up a, ULift.up e)) at h
  rw [pairBoundary_of, lift_apply_of] at h
  rw [hmap a, hmap e]
  exact h.symm.trans (bMap.map_sub (of (ULift.up e)) (of (ULift.up a)))

end
end ManuscriptAudit.InjectiveLiftedYonedaCech

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.InjectiveLiftedYonedaCech.exists_coboundary
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
