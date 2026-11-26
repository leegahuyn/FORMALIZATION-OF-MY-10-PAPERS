import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleBaseChange

/-!
# Affine étale base change and full small étale sheaves

An affine étale base-change equivalence suffices to compare full small étale
sheaves. The two affine inclusions detect covering sieves and are already
comparison equivalences for abelian-group-valued sheaves.
-/

namespace ManuscriptAudit.AffineEtaleBaseChange

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits SmallEtaleBaseChange

universe u v w

noncomputable section

private theorem functorPushforward_eq_pullback_of_iso {C D : Type*} [Category* C] [Category* D]
    {F G : C ⥤ D} (e : F ≅ G) {W : C} (S : Sieve W) :
    S.functorPushforward F = (S.functorPushforward G).pullback (e.hom.app W) := by
  apply Sieve.ext
  intro Z k
  change (∃ (V : C) (g : V ⟶ W) (a : Z ⟶ F.obj V), S g ∧ k = a ≫ F.map g) ↔
    (∃ (V : C) (g : V ⟶ W) (a : Z ⟶ G.obj V), S g ∧ k ≫ e.hom.app W = a ≫ G.map g)
  constructor
  · rintro ⟨V, g, a, hg, rfl⟩
    refine ⟨V, g, a ≫ e.hom.app V, hg, ?_⟩
    simp only [Category.assoc, e.hom.naturality]
  · rintro ⟨V, g, a, hg, ha⟩
    refine ⟨V, g, a ≫ e.inv.app V, hg, ?_⟩
    calc
      k = (k ≫ e.hom.app W) ≫ e.inv.app W := by simp
      _ = (a ≫ G.map g) ≫ e.inv.app W := by rw [ha]
      _ = (a ≫ e.inv.app V) ≫ F.map g := by simp only [Category.assoc, e.inv.naturality]

private theorem functorPushforward_mem_iff_of_iso {C D : Type*} [Category* C] [Category* D]
    {F G : C ⥤ D} (e : F ≅ G) (J : GrothendieckTopology D) {W : C} (S : Sieve W) :
    S.functorPushforward F ∈ J (F.obj W) ↔ S.functorPushforward G ∈ J (G.obj W) := by
  rw [functorPushforward_eq_pullback_of_iso e S,
    GrothendieckTopology.pullback_mem_iff_of_isIso]

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : Function.Surjective f)
variable (E : Y.AffineEtale ⥤ X.AffineEtale)
variable (e : E ⋙ Scheme.AffineEtale.Spec X ≅ Scheme.AffineEtale.Spec Y ⋙ etaleBaseChange f)

include f hf e

/-- Affine étale base change along a surjective morphism preserves and reflects covering sieves. -/
theorem functorPushforward_mem_iff {W : Y.AffineEtale} {S : Sieve W} :
    S.functorPushforward E ∈ Scheme.AffineEtale.topology X _ ↔
      S ∈ Scheme.AffineEtale.topology Y W := by
  calc
    S.functorPushforward E ∈ Scheme.AffineEtale.topology X _ ↔
        (S.functorPushforward E).functorPushforward (Scheme.AffineEtale.Spec X) ∈
          X.smallEtaleTopology _ :=
      ((Scheme.AffineEtale.Spec X).functorPushforward_mem_iff _ _).symm
    _ ↔ S.functorPushforward (Scheme.AffineEtale.Spec Y ⋙ etaleBaseChange f) ∈
        X.smallEtaleTopology _ := by
      rw [← Sieve.functorPushforward_comp]
      exact functorPushforward_mem_iff_of_iso e X.smallEtaleTopology S
    _ ↔ (S.functorPushforward (Scheme.AffineEtale.Spec Y)).functorPushforward (etaleBaseChange f) ∈
        X.smallEtaleTopology _ := by simp only [Sieve.functorPushforward_comp, Functor.comp_obj]
    _ ↔ S.functorPushforward (Scheme.AffineEtale.Spec Y) ∈ Y.smallEtaleTopology _ :=
      SmallEtaleBaseChange.functorPushforward_mem_iff f hf
    _ ↔ S ∈ Scheme.AffineEtale.topology Y W :=
      (Scheme.AffineEtale.Spec Y).functorPushforward_mem_iff _ _

/-- The affine base-change equivalence is an equivalence of covering sieves. -/
theorem isDenseSubsite [E.IsEquivalence] :
    E.IsDenseSubsite (Scheme.AffineEtale.topology Y) (Scheme.AffineEtale.topology X) where
  functorPushforward_mem_iff := functorPushforward_mem_iff f hf E e

/-- An equivalence on affine étale objects identifies sheaf categories on the affine sites. -/
def affineSheafEquivalence [E.IsEquivalence] (C : Type v) [Category.{w} C] :
    Sheaf (Scheme.AffineEtale.topology X) C ≌ Sheaf (Scheme.AffineEtale.topology Y) C := by
  letI := isDenseSubsite f hf E e
  let eCat : X.AffineEtale ≌ Y.AffineEtale := E.asEquivalence.symm
  letI : eCat.inverse.IsDenseSubsite (Scheme.AffineEtale.topology Y)
      (Scheme.AffineEtale.topology X) :=
    inferInstanceAs (E.IsDenseSubsite (Scheme.AffineEtale.topology Y) (Scheme.AffineEtale.topology X))
  exact Equivalence.sheafCongr (Scheme.AffineEtale.topology X)
    (Scheme.AffineEtale.topology Y) eCat C

/-- An affine étale base-change equivalence suffices for full small étale abelian sheaves. -/
def fullSheafEquivalence [E.IsEquivalence] :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ≌ Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} :=
  (Scheme.AffineEtale.sheafEquiv X AddCommGrpCat.{u}).symm.trans
    ((affineSheafEquivalence f hf E e AddCommGrpCat.{u}).trans
      (Scheme.AffineEtale.sheafEquiv Y AddCommGrpCat.{u}))

set_option backward.isDefEq.respectTransparency false in
/-- The actual full direct image is an equivalence whenever it is so on affine étale objects. -/
theorem fullPushforward_isEquivalence [E.IsEquivalence] :
    (sheafPushforward f hf AddCommGrpCat.{u}).IsEquivalence := by
  let fx := Scheme.AffineEtale.Spec X
  let fy := Scheme.AffineEtale.Spec Y
  let gx := Scheme.AffineEtale.topology X
  let gy := Scheme.AffineEtale.topology Y
  letI := isDenseSubsite f hf E e
  letI := SmallEtaleBaseChange.isContinuous f hf
  letI := Functor.isContinuous_comp E fx gy gx X.smallEtaleTopology
  letI := Functor.isContinuous_comp fy (etaleBaseChange f) gy Y.smallEtaleTopology X.smallEtaleTopology
  let px := fx.sheafPushforwardContinuous AddCommGrpCat.{u} gx X.smallEtaleTopology
  let py := fy.sheafPushforwardContinuous AddCommGrpCat.{u} gy Y.smallEtaleTopology
  let pe := E.sheafPushforwardContinuous AddCommGrpCat.{u} gy gx
  let pf := sheafPushforward f hf AddCommGrpCat.{u}
  letI : px.IsEquivalence := inferInstanceAs
    ((Scheme.AffineEtale.Spec X).sheafPushforwardContinuous AddCommGrpCat.{u}
      (Scheme.AffineEtale.topology X) X.smallEtaleTopology).IsEquivalence
  letI : py.IsEquivalence := inferInstanceAs
    ((Scheme.AffineEtale.Spec Y).sheafPushforwardContinuous AddCommGrpCat.{u}
      (Scheme.AffineEtale.topology Y) Y.smallEtaleTopology).IsEquivalence
  letI : pe.IsEquivalence := (affineSheafEquivalence f hf E e AddCommGrpCat.{u}).isEquivalence_functor
  let h : px ⋙ pe ≅ pf ⋙ py :=
    Functor.sheafPushforwardContinuousComp (F := E) (G := fx) (A := AddCommGrpCat.{u})
      (J := gy) (K := gx) (L := X.smallEtaleTopology) ≪≫
    Functor.sheafPushforwardContinuousIso e (A := AddCommGrpCat.{u})
      (J := gy) (K := X.smallEtaleTopology) ≪≫
    (Functor.sheafPushforwardContinuousComp (F := fy) (G := etaleBaseChange f)
      (A := AddCommGrpCat.{u}) (J := gy) (K := Y.smallEtaleTopology) (L := X.smallEtaleTopology)).symm
  letI : (pf ⋙ py).IsEquivalence := Functor.isEquivalence_of_iso h
  exact Functor.isEquivalence_of_comp_right pf py

/-- The canonical equivalence whose forward functor is the actual full direct image. -/
def canonicalFullSheafEquivalence [E.IsEquivalence] :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ≌ Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} :=
  letI := fullPushforward_isEquivalence f hf E e
  (sheafPushforward f hf AddCommGrpCat.{u}).asEquivalence

set_option backward.isDefEq.respectTransparency false in
/-- The inverse of the actual direct-image equivalence takes constant sheaves to constants. -/
def canonicalPullbackConstantComparison [E.IsEquivalence] :
    constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u} ⋙
      (canonicalFullSheafEquivalence f hf E e).inverse ≅
        constantSheaf X.smallEtaleTopology AddCommGrpCat.{u} := by
  letI := SmallEtaleBaseChange.preservesFiniteLimits f
  let k := canonicalFullSheafEquivalence f hf E e
  let ay := constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u}
    (terminalIsTerminal (C := Y.Etale))
  let ax := constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u}
    (isLimitOfHasTerminalOfPreservesLimit (etaleBaseChange f))
  exact (ay.comp k.symm.toAdjunction).leftAdjointUniq ax

set_option backward.isDefEq.respectTransparency false in
/-- The actual direct image takes constant sheaves to constants. -/
def canonicalConstantComparison [E.IsEquivalence] :
    constantSheaf X.smallEtaleTopology AddCommGrpCat.{u} ⋙
      sheafPushforward f hf AddCommGrpCat.{u} ≅
        constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u} := by
  let k := canonicalFullSheafEquivalence f hf E e
  let cy := constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}
  let c := canonicalPullbackConstantComparison f hf E e
  exact (Functor.isoWhiskerRight c k.functor).symm ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft cy k.counitIso ≪≫ cy.rightUnitor

end

end ManuscriptAudit.AffineEtaleBaseChange

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.AffineEtaleBaseChange.functorPushforward_mem_iff,
      ``ManuscriptAudit.AffineEtaleBaseChange.affineSheafEquivalence,
      ``ManuscriptAudit.AffineEtaleBaseChange.fullSheafEquivalence,
      ``ManuscriptAudit.AffineEtaleBaseChange.fullPushforward_isEquivalence,
      ``ManuscriptAudit.AffineEtaleBaseChange.canonicalFullSheafEquivalence,
      ``ManuscriptAudit.AffineEtaleBaseChange.canonicalPullbackConstantComparison,
      ``ManuscriptAudit.AffineEtaleBaseChange.canonicalConstantComparison] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
