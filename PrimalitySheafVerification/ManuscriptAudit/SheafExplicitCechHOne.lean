import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.SheafSectionDifference
import PrimalitySheafVerification.ManuscriptAudit.SingletonCoverRefinement

/-! Explicit cartesian overlaps suffice to descend degree-one abelian
sheaf sections. The argument uses the given pullback projections
and three commuting face maps. -/

namespace ManuscriptAudit.SheafExplicitCechHOne

open CategoryTheory CategoryTheory.Limits Opposite
open SingletonCoverRefinement

universe u v w
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
  {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{w}]
  {F I : Sheaf J AddCommGrpCat.{w}} (i : F ⟶ I) [Mono i]
  {U T P E : C} (f : U ⟶ T) (p₀ p₁ : P ⟶ U)
  (hP : IsPullback p₀ p₁ f f)

private theorem restrict_restrict (A : Sheaf J AddCommGrpCat.{w}) {X Y Z : C}
    (a : X ⟶ Y) (b : Y ⟶ Z) (x : A.obj.obj (op Z)) :
    A.obj.map a.op (A.obj.map b.op x) = A.obj.map (a ≫ b).op x := by
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

/-- The local difference gives a cocycle on the given concrete double
overlap, with the actual three face maps of a triple overlap. -/
theorem exists_cocycle (e₀₁ e₀₂ e₁₂ : E ⟶ P)
    (h₀ : e₀₂ ≫ p₀ = e₀₁ ≫ p₀) (h₁ : e₁₂ ≫ p₀ = e₀₁ ≫ p₁)
    (h₂ : e₁₂ ≫ p₁ = e₀₂ ≫ p₁)
    (x : (cokernel i).obj.obj (op T)) (y : I.obj.obj (op U))
    (hy : (cokernel.π i).hom.app (op U) y = (cokernel i).obj.map f.op x) :
    ∃ b : F.obj.obj (op P),
      i.hom.app (op P) b = I.obj.map p₁.op y - I.obj.map p₀.op y ∧
      F.obj.map e₁₂.op b - F.obj.map e₀₂.op b + F.obj.map e₀₁.op b = 0 := by
  let π := cokernel.π i
  have he : π.hom.app (op P) (I.obj.map p₁.op y) =
      π.hom.app (op P) (I.obj.map p₀.op y) := by
    rw [NatTrans.naturality_apply π.hom p₁.op y, NatTrans.naturality_apply π.hom p₀.op y, hy,
      restrict_restrict, restrict_restrict, hP.w]
  let b := SheafSectionDifference.difference i P (I.obj.map p₁.op y) (I.obj.map p₀.op y) he
  have hb : i.hom.app (op P) b = I.obj.map p₁.op y - I.obj.map p₀.op y :=
    SheafSectionDifference.difference_spec i P _ _ he
  refine ⟨b, hb, ?_⟩
  apply SheafSectionDifference.section_injective i E
  have h (d : E ⟶ P) : i.hom.app (op E) (F.obj.map d.op b) =
      I.obj.map (d ≫ p₁).op y - I.obj.map (d ≫ p₀).op y := by
    rw [NatTrans.naturality_apply i.hom d.op b, hb]
    change (I.obj.map d.op).hom (I.obj.map p₁.op y - I.obj.map p₀.op y) = _
    rw [map_sub]
    exact congrArg₂ (fun a b : I.obj.obj (op E) ↦ a - b)
      (restrict_restrict I d p₁ y) (restrict_restrict I d p₀ y)
  change (i.hom.app (op E)).hom
    (F.obj.map e₁₂.op b - F.obj.map e₀₂.op b + F.obj.map e₀₁.op b) =
      (i.hom.app (op E)).hom 0
  rw [map_add, map_sub, map_zero]
  change i.hom.app _ (F.obj.map e₁₂.op b) - i.hom.app _ (F.obj.map e₀₂.op b) +
    i.hom.app _ (F.obj.map e₀₁.op b) = 0
  rw [h e₁₂, h e₀₂, h e₀₁, h₀, h₁, h₂]
  abel

variable [J.HasSheafCompose (forget AddCommGrpCat.{w})]

/-- A local primitive for the double-overlap difference gives a global
cokernel lift. -/
theorem exists_global_lift (hf : Covers J f)
    (x : (cokernel i).obj.obj (op T)) (y : I.obj.obj (op U))
    (hy : (cokernel.π i).hom.app (op U) y = (cokernel i).obj.map f.op x)
    (a : F.obj.obj (op U))
    (ha : i.hom.app (op P) (F.obj.map p₁.op a - F.obj.map p₀.op a) =
      I.obj.map p₁.op y - I.obj.map p₀.op y) :
    ∃ z : I.obj.obj (op T), (cokernel.π i).hom.app (op T) z = x := by
  let k := i.hom.app (op U)
  let y' := y - k a
  have hDiff : I.obj.map p₁.op (k a) - I.obj.map p₀.op (k a) =
      I.obj.map p₁.op y - I.obj.map p₀.op y := by
    change I.obj.map p₁.op (i.hom.app (op U) a) -
      I.obj.map p₀.op (i.hom.app (op U) a) = _
    rw [← NatTrans.naturality_apply i.hom p₁.op a, ← NatTrans.naturality_apply i.hom p₀.op a]
    change (i.hom.app (op P)).hom _ - (i.hom.app (op P)).hom _ = _
    rwa [← map_sub]
  have hCompat : I.obj.map p₀.op y' = I.obj.map p₁.op y' := by
    apply Eq.symm
    apply sub_eq_zero.mp
    change (I.obj.map p₁.op).hom (y - k a) - (I.obj.map p₀.op).hom (y - k a) = 0
    rw [map_sub, map_sub]
    calc
      _ = (I.obj.map p₁.op y - I.obj.map p₀.op y) -
        (I.obj.map p₁.op (k a) - I.obj.map p₀.op (k a)) := by abel
      _ = 0 := by rw [hDiff, sub_self]
  have hPull : I.obj.map (pullback.fst f f).op y' = I.obj.map (pullback.snd f f).op y' := by
    rw [← hP.isoPullback_inv_fst, ← hP.isoPullback_inv_snd,
      ← restrict_restrict, ← restrict_restrict, hCompat]
  let π := cokernel.π i
  have hZero : π.hom.app (op U) (k a) = 0 :=
    ConcreteCategory.congr_hom (congrArg (fun e : F ⟶ cokernel i ↦ e.hom.app (op U))
      (cokernel.condition i)) a
  have hImage : π.hom.app (op U) y' = (cokernel i).obj.map f.op x := by
    change (π.hom.app (op U)).hom (y - k a) = _
    rw [map_sub]
    change π.hom.app (op U) y - π.hom.app (op U) (k a) = _
    rw [hZero, sub_zero]
    exact hy
  obtain ⟨z, hz⟩ := exists_amalgamation J I f hf y' hPull
  refine ⟨z, restriction_injective J (cokernel i) f hf ?_⟩
  rw [← NatTrans.naturality_apply π.hom f.op z, hz]
  exact hImage

end
end ManuscriptAudit.SheafExplicitCechHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.SheafExplicitCechHOne.exists_cocycle,
      ``ManuscriptAudit.SheafExplicitCechHOne.exists_global_lift] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
