import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleFiniteCover
import PrimalitySheafVerification.ManuscriptAudit.FiniteSupportEtalePresheaf

/-!
# Finite-support sheaves on the small affine étale site

Components of a compatible family glue separately. A finite covering
subfamily bounds the support of each glued section. This proves that
the actual pointwise direct sum satisfies the sheaf condition.
-/

namespace ManuscriptAudit.FiniteSupportPresheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)

/-- Every covering family has a finite covering subfamily. -/
def HasFiniteCoverFamilies : Prop :=
  ∀ {U : C} {I : Type (max u v)} (V : I → C) (f : ∀ i, V i ⟶ U),
    Sieve.ofArrows V f ∈ J U →
    ∃ t : Finset I, Sieve.ofArrows (fun i : t ↦ V i.val) (fun i : t ↦ f i.val) ∈ J U

private theorem sheafForArrows (F : Sheaf J AddCommGrpCat.{0}) (E : AddCommGrpCat.{0})
    {U : C} {I : Type*} (V : I → C) (f : ∀ i, V i ⟶ U) (hf : Sieve.ofArrows V f ∈ J U) :
    Presieve.IsSheafFor (F.obj ⋙ coyoneda.obj (op E)) (Presieve.ofArrows V f) :=
  (Presieve.isSheafFor_iff_generate _).mpr (F.property E _ hf)

private def integerHom {A : AddCommGrpCat.{0}} (x : A) : AddCommGrpCat.of ℤ ⟶ A :=
  AddCommGrpCat.ofHom
    { toFun := fun n ↦ n • x
      map_zero' := zero_zsmul x
      map_add' := fun _ _ ↦ add_zsmul _ _ _ }

private theorem element_eq_zero_of_cover (F : Sheaf J AddCommGrpCat.{0})
    {U : C} {I : Type*} (V : I → C) (f : ∀ i, V i ⟶ U) (hf : Sieve.ofArrows V f ∈ J U)
    (x : F.obj.obj (op U)) (hx : ∀ i, F.obj.map (f i).op x = 0) : x = 0 := by
  let E := AddCommGrpCat.of ℤ
  let h : E ⟶ F.obj.obj (op U) := integerHom x
  have hh : h = 0 := by
    apply (sheafForArrows J F E V f hf).isSeparatedFor.ext
    rintro _ _ ⟨i⟩
    change h ≫ F.obj.map (f i).op = 0 ≫ F.obj.map (f i).op
    rw [zero_comp]
    apply ConcreteCategory.hom_ext
    intro n
    change (F.obj.map (f i).op).hom (n • x) = 0
    rw [map_zsmul, show (F.obj.map (f i).op).hom x = 0 from hx i, zsmul_zero]
  have hOne := ConcreteCategory.congr_hom hh (1 : ℤ)
  change (1 : ℤ) • x = 0 at hOne
  rwa [one_zsmul] at hOne

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
/-- Pointwise finite-support families of sheaves glue on a site with finite subcovers. -/
theorem directSum_isSheaf (hFinite : HasFiniteCoverFamilies J) {ι : Type}
    (P : ι → Sheaf J AddCommGrpCat.{0}) :
    Presheaf.IsSheaf J (directSum (fun a ↦ (P a).obj)) := by
  classical
  let F := fun a ↦ (P a).obj
  let Q := directSum F
  intro E U S hS
  obtain ⟨I, V, f, rfl⟩ := S.exists_eq_ofArrows
  apply (Presieve.isSheafFor_iff_generate (Presieve.ofArrows V f)).mp
  apply (Presieve.isSheafFor_arrows_iff (P := Q ⋙ coyoneda.obj (op E)) (π := f)).mpr
  intro x hx
  let x' (i : I) : E ⟶ Q.obj (op (V i)) := x i
  let xval (i : I) (z : E) : sections F (op (V i)) := x' i z
  let q (a : ι) (i : I) : E ⟶ (F a).obj (op (V i)) :=
    x' i ≫ (component F a).app (op (V i))
  have hq (a : ι) : Presieve.Arrows.Compatible (F a ⋙ coyoneda.obj (op E)) f (q a) := by
    intro i j W gi gj h
    let e := component F a
    have hh : x' i ≫ Q.map gi.op = x' j ≫ Q.map gj.op := hx i j W gi gj h
    change (x' i ≫ e.app (op (V i))) ≫ (F a).map gi.op =
      (x' j ≫ e.app (op (V j))) ≫ (F a).map gj.op
    calc
      _ = (x' i ≫ Q.map gi.op) ≫ e.app (op W) := by
        rw [Category.assoc, ← e.naturality, Category.assoc]
      _ = (x' j ≫ Q.map gj.op) ≫ e.app (op W) := by rw [hh]
      _ = _ := by simp only [Category.assoc, e.naturality gj.op]
  have hGlue (a : ι) :
      ∃! y : E ⟶ (F a).obj (op U), ∀ i, y ≫ (F a).map (f i).op = q a i :=
    (Presieve.isSheafFor_arrows_iff (P := F a ⋙ coyoneda.obj (op E)) (π := f)).mp
      (sheafForArrows J (P a) E V f hS) (q a) (hq a)
  choose y hy hyu using hGlue
  obtain ⟨t, ht⟩ := hFinite V f hS
  let bounds (z : E) := t.biUnion (fun i ↦ (xval i z).support)
  have hZero (z : E) (a : ι) (ha : a ∉ bounds z) : y a z = 0 := by
    apply element_eq_zero_of_cover J (P a) (fun i : t ↦ V i.val) (fun i : t ↦ f i.val) ht
    intro i
    have h₁ : (F a).map (f i.val).op (y a z) = (xval i.val z) a :=
      ConcreteCategory.congr_hom (hy a i.val) z
    rw [h₁]
    by_contra hn
    exact ha (Finset.mem_biUnion.mpr ⟨i.val, i.property,
      (DFinsupp.mem_support_toFun (xval i.val z) a).mpr hn⟩)
  let value (z : E) : sections F (op U) :=
    ⟨fun a ↦ y a z, Trunc.mk ⟨(bounds z).val, fun a ↦ by
      by_cases ha : a ∈ bounds z
      · exact Or.inl ha
      · exact Or.inr (hZero z a ha)⟩⟩
  let m : E ⟶ Q.obj (op U) := AddCommGrpCat.ofHom
    { toFun := value
      map_zero' := DFinsupp.ext fun a ↦ (y a).hom.map_zero
      map_add' := fun z w ↦ DFinsupp.ext fun a ↦ (y a).hom.map_add z w }
  refine ⟨m, ?_, ?_⟩
  · intro i
    change m ≫ Q.map (f i).op = x' i
    apply ConcreteCategory.hom_ext
    intro z
    apply DFinsupp.ext
    intro a
    exact ConcreteCategory.congr_hom (hy a i) z
  · intro n hn
    have hna (a : ι) : n ≫ (component F a).app (op U) = y a := by
      apply hyu a
      intro i
      let e := component F a
      change (n ≫ e.app (op U)) ≫ (F a).map (f i).op = x' i ≫ e.app (op (V i))
      rw [Category.assoc, ← e.naturality, ← Category.assoc]
      have hi : n ≫ Q.map (f i).op = x' i := hn i
      rw [hi]
    apply ConcreteCategory.hom_ext
    intro z
    apply DFinsupp.ext
    intro a
    exact ConcreteCategory.congr_hom (hna a) z

/-- The finite-support presheaf of affine étale sheaves is an actual sheaf. -/
def affineEtaleDirectSum (S : Scheme.{u}) {ι : Type}
    (P : ι → Sheaf (Scheme.AffineEtale.topology S) AddCommGrpCat.{0}) :
    Sheaf (Scheme.AffineEtale.topology S) AddCommGrpCat.{0} :=
  ⟨directSum (fun a ↦ (P a).obj), directSum_isSheaf _ (fun V f h ↦
    AffineEtaleFiniteCover.finiteSubcover_ofArrows V f h) P⟩

end

end ManuscriptAudit.FiniteSupportPresheaf

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.FiniteSupportPresheaf.directSum_isSheaf,
      ``ManuscriptAudit.FiniteSupportPresheaf.affineEtaleDirectSum] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
