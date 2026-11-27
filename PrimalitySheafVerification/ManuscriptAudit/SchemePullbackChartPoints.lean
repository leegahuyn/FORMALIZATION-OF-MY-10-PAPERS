import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleContinuousDirectImageMaps

/-! Cartesian open chart restriction of an arbitrary pullback, with the
induced map of actual geometric points and functoriality on both branches. -/

namespace ManuscriptAudit.SchemePullbackChartPoints

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ProetaleContinuousDirectImageMaps (pullbackMap pullbackMap_fst pullbackMap_snd)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

theorem points_lift {P U V X : Scheme.{0}}
    {a : P ⟶ U} {b : P ⟶ V} {f : U ⟶ X} {g : V ⟶ X}
    (H : IsPullback a b f g) (u : U) (v : V) (h : f u = g v) :
    ∃ t : P, a t = u ∧ b t = v := by
  obtain ⟨s, hs, hs'⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) u v h
  refine ⟨H.isoPullback.inv s, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, H.isoPullback_inv_fst, hs]
  · rw [← Scheme.Hom.comp_apply, H.isoPullback_inv_snd, hs']

variable {V W Z X L N O : Scheme.{0}}
  (m : V ⟶ W) (z : V ⟶ Z) (a : W ⟶ X) (j : Z ⟶ X)
  (h : z ≫ j = m ≫ a)
  (n : L ⟶ Z) (e : L ⟶ N) (p : N ⟶ X) (he : e ≫ p = n ≫ j)

/-- The map from the chart model to the actual ambient pullback. -/
def fromChart : pullback z n ⟶ pullback a p :=
  pullback.lift (pullback.fst z n ≫ m) (pullback.snd z n ≫ e) (by
    calc
      (pullback.fst z n ≫ m) ≫ a = (pullback.fst z n ≫ z) ≫ j := by
        rw [Category.assoc, ← h, Category.assoc]
      _ = (pullback.snd z n ≫ n) ≫ j := by rw [pullback.condition]
      _ = (pullback.snd z n ≫ e) ≫ p := by rw [Category.assoc, Category.assoc, he])

@[reassoc]
theorem fromChart_fst : fromChart m z a j h n e p he ≫ pullback.fst a p =
    pullback.fst z n ≫ m := pullback.lift_fst _ _ _

@[reassoc]
theorem fromChart_snd : fromChart m z a j h n e p he ≫ pullback.snd a p =
    pullback.snd z n ≫ e := pullback.lift_snd _ _ _

/-- If the displayed chart is Cartesian, its pullback is the restriction
of the ambient pullback to the indicated chart of the arbitrary source. -/
theorem fromChart_isPullback (H : IsPullback e n p j) :
    IsPullback (fromChart m z a j h n e p H.w) (pullback.fst z n)
      (pullback.fst a p) m := by
  refine IsPullback.of_right ?_ (fromChart_fst m z a j h n e p H.w)
    (IsPullback.of_hasPullback a p).flip
  rw [fromChart_snd, ← h]
  exact (IsPullback.of_hasPullback z n).flip.paste_horiz H

variable (i : O ⟶ Z) (b : O ⟶ L) (hb : b ≫ n = i)

theorem branch_ambient_comp : (b ≫ e) ≫ p = i ≫ j := by
  rw [Category.assoc, he, ← Category.assoc, hb]

/-- Restriction to a genuine chart commutes with either ordered branch. -/
theorem fromChart_branch :
    pullbackMap z b hb ≫ fromChart m z a j h n e p he =
      fromChart m z a j h i (𝟙 O) (i ≫ j) (Category.id_comp _) ≫
        pullbackMap a (b ≫ e) (branch_ambient_comp j n e p he i b hb) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, fromChart_fst, pullbackMap_fst, pullbackMap_fst_assoc]
  · simp only [Category.assoc, fromChart_snd, pullbackMap_snd, pullbackMap_snd_assoc,
      fromChart_snd_assoc, Category.id_comp]

end
end ManuscriptAudit.SchemePullbackChartPoints

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.SchemePullbackChartPoints.points_lift,
      ``ManuscriptAudit.SchemePullbackChartPoints.fromChart_isPullback,
      ``ManuscriptAudit.SchemePullbackChartPoints.fromChart_branch] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
