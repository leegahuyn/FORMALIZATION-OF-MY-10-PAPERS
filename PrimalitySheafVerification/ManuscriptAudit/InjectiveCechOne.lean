import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Sites.Abelian
import PrimalitySheafVerification.ManuscriptAudit.FreeAbelianPairBoundary

/-! Every single-object Čech one-cocycle of an injective abelian sheaf is a coboundary. -/

namespace ManuscriptAudit.InjectiveCechOne

open CategoryTheory CategoryTheory.Limits Opposite
open FreeAbelianGroup
open FreeAbelianPairBoundary

universe v u
variable {C : Type u} [Category.{v} C]

noncomputable section

private def pairTypes (U : C) : Cᵒᵖ ⥤ Type v where
  obj W := (unop W ⟶ U) × (unop W ⟶ U)
  map f := TypeCat.ofHom fun p => (f.unop ≫ p.1, f.unop ≫ p.2)
  map_id W := by
    apply ConcreteCategory.hom_ext
    rintro ⟨a, b⟩
    change (𝟙 _ ≫ a, 𝟙 _ ≫ b) = (a, b)
    simp
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    rintro ⟨a, b⟩
    change ((g.unop ≫ f.unop) ≫ a, (g.unop ≫ f.unop) ≫ b) =
      (g.unop ≫ f.unop ≫ a, g.unop ≫ f.unop ≫ b)
    simp only [Category.assoc]

private def tripleTypes (U : C) : Cᵒᵖ ⥤ Type v where
  obj W := (unop W ⟶ U) × (unop W ⟶ U) × (unop W ⟶ U)
  map f := TypeCat.ofHom fun p => (f.unop ≫ p.1, f.unop ≫ p.2.1, f.unop ≫ p.2.2)
  map_id W := by
    apply ConcreteCategory.hom_ext
    rintro ⟨a, b, c⟩
    change (𝟙 _ ≫ a, 𝟙 _ ≫ b, 𝟙 _ ≫ c) = (a, b, c)
    simp
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    rintro ⟨a, b, c⟩
    change ((g.unop ≫ f.unop) ≫ a, (g.unop ≫ f.unop) ≫ b, (g.unop ≫ f.unop) ≫ c) =
      (g.unop ≫ f.unop ≫ a, g.unop ≫ f.unop ≫ b, g.unop ≫ f.unop ≫ c)
    simp only [Category.assoc]

private abbrev singles (U : C) := yoneda.obj U ⋙ AddCommGrpCat.free
private abbrev pairs (U : C) := pairTypes U ⋙ AddCommGrpCat.free
private abbrev triples (U : C) := tripleTypes U ⋙ AddCommGrpCat.free

private def dOne (U : C) : pairs U ⟶ singles U where
  app W := AddCommGrpCat.ofHom (pairBoundary (unop W ⟶ U))
  naturality {W V} f := by
    apply AddCommGrpCat.hom_ext
    change (pairBoundary _).comp (FreeAbelianGroup.map (fun p => (f.unop ≫ p.1, f.unop ≫ p.2))) =
      (FreeAbelianGroup.map (fun h => f.unop ≫ h)).comp (pairBoundary _)
    apply lift_ext
    rintro ⟨a, b⟩
    simp only [AddMonoidHom.comp_apply, map_of_apply, pairBoundary_of, map_sub]

private def dTwo (U : C) : triples U ⟶ pairs U where
  app W := AddCommGrpCat.ofHom (tripleBoundary (unop W ⟶ U))
  naturality {W V} f := by
    apply AddCommGrpCat.hom_ext
    change (tripleBoundary _).comp (FreeAbelianGroup.map (fun p =>
        (f.unop ≫ p.1, f.unop ≫ p.2.1, f.unop ≫ p.2.2))) =
      (FreeAbelianGroup.map (fun p => (f.unop ≫ p.1, f.unop ≫ p.2))).comp (tripleBoundary _)
    apply lift_ext
    rintro ⟨a, b, c⟩
    simp only [AddMonoidHom.comp_apply, map_of_apply, tripleBoundary_of, map_sub, map_add]

private theorem dTwo_dOne (U : C) : dTwo U ≫ dOne U = 0 := by
  ext1
  funext W
  apply AddCommGrpCat.hom_ext
  exact pairBoundary_comp_tripleBoundary (unop W ⟶ U)

private def complex (U : C) : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat.{v}) :=
  ShortComplex.mk (dTwo U) (dOne U) (dTwo_dOne U)

private theorem complex_exact (U : C) : (complex U).Exact := by
  let S := complex U
  change S.Exact
  rw [S.exact_iff_kernel_ι_comp_cokernel_π_zero]
  ext1
  funext W
  let E := (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{v}).obj W
  have hE : (S.map E).Exact := by
    rw [(S.map E).ab_exact_iff]
    exact exists_tripleBoundary_of_pairBoundary_eq_zero (unop W ⟶ U)
  have hZ := (S.map E).exact_iff_kernel_ι_comp_cokernel_π_zero.mp hE
  change E.map (kernel.ι S.g) ≫ E.map (cokernel.π S.f) = 0
  rw [← kernelComparison_comp_ι S.g E, ← π_comp_cokernelComparison S.f E,
    Category.assoc, ← Category.assoc (kernel.ι (E.map S.g)), hZ, zero_comp, comp_zero]

variable (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{v}]

/-- A cocycle is specified by its values for every pair of arrows into the cover. -/
theorem exists_coboundary (U : C) (I : Sheaf J AddCommGrpCat.{v}) [Injective I]
    (c : ∀ {W : C}, (W ⟶ U) → (W ⟶ U) → I.obj.obj (op W))
    (hnat : ∀ {W V : C} (r : V ⟶ W) (a b : W ⟶ U),
      I.obj.map r.op (c a b) = c (r ≫ a) (r ≫ b))
    (hc : ∀ {W : C} (a b d : W ⟶ U), c b d - c a d + c a b = 0) :
    ∃ b : I.obj.obj (op U), ∀ {W : C} (a d : W ⟶ U),
      c a d = I.obj.map d.op b - I.obj.map a.op b := by
  let z : pairs U ⟶ I.obj :=
    { app := fun W => AddCommGrpCat.ofHom (lift fun p => c p.1 p.2)
      naturality := by
        intro W V f
        apply AddCommGrpCat.hom_ext
        change (lift (fun p : (unop V ⟶ U) × (unop V ⟶ U) => c p.1 p.2)).comp
          (FreeAbelianGroup.map (fun p : (unop W ⟶ U) × (unop W ⟶ U) =>
            (f.unop ≫ p.1, f.unop ≫ p.2))) =
          (I.obj.map f).hom.comp (lift (fun p : (unop W ⟶ U) × (unop W ⟶ U) => c p.1 p.2))
        apply lift_ext
        rintro ⟨a, b⟩
        rw [AddMonoidHom.comp_apply, map_of_apply, lift_apply_of,
          AddMonoidHom.comp_apply, lift_apply_of]
        exact (hnat f.unop a b).symm }
  have hz : dTwo U ≫ z = 0 := by
    ext1
    funext W
    apply AddCommGrpCat.hom_ext
    let m : FreeAbelianGroup ((unop W ⟶ U) × (unop W ⟶ U)) →+ I.obj.obj W :=
      lift (fun p => c p.1 p.2)
    change m.comp (tripleBoundary _) = 0
    apply lift_ext
    rintro ⟨a, b, d⟩
    rw [AddMonoidHom.comp_apply, tripleBoundary_of, m.map_add, m.map_sub]
    exact hc a b d
  let k := cokernel.desc (dTwo U) (dOne U) (dTwo_dOne U)
  letI : Mono k := (complex U).exact_iff_mono_cokernel_desc.mp (complex_exact U)
  let zbar := cokernel.desc (dTwo U) z hz
  let A := sheafificationAdjunction J AddCommGrpCat.{v}
  let zb := (A.homEquiv _ I).symm zbar
  letI : Mono ((presheafToSheaf J AddCommGrpCat.{v}).map k) := inferInstance
  obtain ⟨bSheaf, hbSheaf⟩ := Injective.factors zb ((presheafToSheaf J AddCommGrpCat.{v}).map k)
  let bPresheaf := A.homEquiv _ I bSheaf
  have hb : k ≫ bPresheaf = zbar := by
    rw [← A.homEquiv_naturality_left, hbSheaf]
    exact (A.homEquiv _ I).apply_symm_apply zbar
  have hfac : dOne U ≫ bPresheaf = z := by
    calc
      dOne U ≫ bPresheaf = cokernel.π (dTwo U) ≫ k ≫ bPresheaf := by
        rw [← Category.assoc, cokernel.π_desc]
      _ = z := by rw [hb]; exact cokernel.π_desc _ _ _
  let b := (bPresheaf.app (op U)).hom (of (𝟙 U))
  refine ⟨b, ?_⟩
  intro W a d
  have hmap (r : W ⟶ U) : I.obj.map r.op b =
      (bPresheaf.app (op W)).hom (of r) := by
    have h := congrArg (fun m : (singles U).obj (op U) ⟶ I.obj.obj (op W) =>
      m.hom (of (𝟙 U))) (bPresheaf.naturality r.op)
    change (bPresheaf.app (op W)).hom (FreeAbelianGroup.map (fun t => r ≫ t) (of (𝟙 U))) =
      I.obj.map r.op b at h
    simpa only [map_of_apply, Category.comp_id] using h.symm
  have h := congrArg (fun m : pairs U ⟶ I.obj =>
    (m.app (op W)).hom (of (a, d))) hfac
  change (bPresheaf.app (op W)).hom (pairBoundary _ (of (a, d))) =
    lift (fun p => c p.1 p.2) (of (a, d)) at h
  rw [pairBoundary_of, (bPresheaf.app (op W)).hom.map_sub, lift_apply_of] at h
  rw [hmap a, hmap d]
  exact h.symm

end
end ManuscriptAudit.InjectiveCechOne

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.InjectiveCechOne.exists_coboundary
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
