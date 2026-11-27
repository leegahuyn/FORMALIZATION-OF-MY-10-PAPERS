import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.TwoOpenCokernelLift

/-! Sections of an abelian sheaf glue across an actual two-object
monomorphic covering family. -/

namespace ManuscriptAudit.TwoOpenSectionGluing

open CategoryTheory CategoryTheory.Limits Opposite
open TwoOpenCokernelLift (coverObjects coverArrows)

universe u v w
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget AddCommGrpCat.{w})] (F : Sheaf J AddCommGrpCat.{w})
  {T U V D : C} (u : U ⟶ T) (v : V ⟶ T) [Mono u] [Mono v]
  (p : D ⟶ U) (q : D ⟶ V) (hD : IsPullback p q u v)
  (hCover : Sieve.ofArrows (coverObjects U V) (coverArrows u v) ∈ J T)

private theorem restrict_restrict {X Y Z : C} (a : X ⟶ Y) (b : Y ⟶ Z)
    (x : F.obj.obj (op Z)) : F.obj.map a.op (F.obj.map b.op x) = F.obj.map (a ≫ b).op x := by
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

include hD hCover in
/-- The overlap equality is the complete gluing criterion for a two-open cover. -/
theorem existsUnique_gluing (a : F.obj.obj (op U)) (b : F.obj.obj (op V))
    (hab : F.obj.map p.op a = F.obj.map q.op b) :
    ∃! z : F.obj.obj (op T), F.obj.map u.op z = a ∧ F.obj.map v.op z = b := by
  let P := F.obj ⋙ forget AddCommGrpCat.{w}
  have hF : Presieve.IsSheaf J P :=
    (isSheaf_iff_isSheaf_of_type J _).mp ((sheafCompose J (forget AddCommGrpCat.{w})).obj F).property
  let y (d : Bool) : P.obj (op (coverObjects U V d)) :=
    match d with
    | false => a
    | true => b
  have cross {W : C} (f : W ⟶ U) (g : W ⟶ V) (h : f ≫ u = g ≫ v) :
      F.obj.map f.op a = F.obj.map g.op b := by
    let l := hD.lift f g h
    calc
      _ = F.obj.map l.op (F.obj.map p.op a) := by rw [restrict_restrict, hD.lift_fst]
      _ = F.obj.map l.op (F.obj.map q.op b) := by rw [hab]
      _ = _ := by rw [restrict_restrict, hD.lift_snd]
  have hCompat : Presieve.Arrows.Compatible P (coverArrows u v) y := by
    intro i j W f g h
    cases i <;> cases j
    · change f ≫ u = g ≫ u at h
      cases (cancel_mono u).mp h
      rfl
    · exact cross f g h
    · exact (cross g f h.symm).symm
    · change f ≫ v = g ≫ v at h
      cases (cancel_mono v).mp h
      rfl
  obtain ⟨z, hz, huniq⟩ := (Presieve.isSheafFor_arrows_iff (P := P) (coverArrows u v)).mp
    (hF.isSheafFor _ hCover) y hCompat
  refine ⟨z, ⟨hz false, hz true⟩, fun z' hz' ↦ huniq z' ?_⟩
  intro d
  cases d
  · exact hz'.1
  · exact hz'.2

include hD hCover in
/-- When the second restriction on the intersection always extends
uniquely to the first piece, restriction to the second piece is bijective. -/
theorem restriction_bijective
    (hInj : Function.Injective (F.obj.map p.op))
    (hExtend : ∀ b : F.obj.obj (op V), ∃ a : F.obj.obj (op U),
      F.obj.map p.op a = F.obj.map q.op b) :
    Function.Bijective (F.obj.map v.op) := by
  constructor
  · intro x y h
    have hx : F.obj.map p.op (F.obj.map u.op x) = F.obj.map q.op (F.obj.map v.op x) := by
      rw [restrict_restrict, restrict_restrict, hD.w]
    have hy : F.obj.map p.op (F.obj.map u.op y) = F.obj.map q.op (F.obj.map v.op y) := by
      rw [restrict_restrict, restrict_restrict, hD.w]
    have hu : F.obj.map u.op x = F.obj.map u.op y := by
      apply hInj
      rw [hx, hy, h]
    obtain ⟨z, _, hz⟩ := existsUnique_gluing F u v p q hD hCover
      (F.obj.map u.op y) (F.obj.map v.op y) hy
    exact (hz x ⟨hu, h⟩).trans (hz y ⟨rfl, rfl⟩).symm
  · intro b
    obtain ⟨a, ha⟩ := hExtend b
    obtain ⟨z, hz, _⟩ := existsUnique_gluing F u v p q hD hCover a b ha
    exact ⟨z, hz.2⟩

end
end ManuscriptAudit.TwoOpenSectionGluing

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.TwoOpenSectionGluing.existsUnique_gluing,
      ``ManuscriptAudit.TwoOpenSectionGluing.restriction_bijective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
