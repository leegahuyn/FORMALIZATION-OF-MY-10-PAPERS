import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleContinuousDirectImageMaps

/-! The actual branch maps commute with transport from an affine
normalization chart to the ambient normalization pullback. -/

namespace ManuscriptAudit.NormalizationBranchChartTransport

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ProetaleContinuousDirectImageMaps (pullbackMap pullbackMap_fst pullbackMap_snd)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {W Y X L N O : Scheme.{0}}
  (a : W ⟶ Y) (j : Y ⟶ X) [Mono j]
  (n : L ⟶ Y) (e : L ⟶ N) (p : N ⟶ X) (hn : IsPullback e n p j)
  (i : O ⟶ Y)

include hn in
private theorem normSquare :
    IsPullback (pullback.fst a n) (pullback.snd a n ≫ e) (a ≫ j) p :=
  ((IsPullback.of_hasPullback a n).flip.paste_horiz hn).flip

include hn in
/-- The actual affine normalization pullback and ambient normalization pullback agree. -/
def normIso : pullback a n ≅ pullback (a ≫ j) p :=
  (normSquare a j n e p hn).isoPullback

theorem normIso_hom_fst :
    (normIso a j n e p hn).hom ≫ pullback.fst (a ≫ j) p = pullback.fst a n :=
  (normSquare a j n e p hn).isoPullback_hom_fst

theorem normIso_hom_snd :
    (normIso a j n e p hn).hom ≫ pullback.snd (a ≫ j) p = pullback.snd a n ≫ e :=
  (normSquare a j n e p hn).isoPullback_hom_snd

private theorem conductorSquare :
    IsPullback (pullback.fst a i) (pullback.snd a i) (a ≫ j) (i ≫ j) := by
  let h := IsPullback.of_hasPullback a i
  refine IsPullback.mk' ?_ (fun {_ _ _} h₁ h₂ ↦ h.hom_ext h₁ h₂) ?_
  · simpa only [← Category.assoc] using
      congrArg (fun f : pullback a i ⟶ Y ↦ f ≫ j) h.w
  · intro T u v hu
    exact h.exists_lift u v ((cancel_mono j).mp (by simpa only [Category.assoc] using hu))

/-- The actual affine conductor pullback identifies with the ambient conductor pullback. -/
def conductorIso : pullback a i ≅ pullback (a ≫ j) (i ≫ j) :=
  (conductorSquare a j i).isoPullback

theorem conductorIso_hom_fst :
    (conductorIso a j i).hom ≫ pullback.fst (a ≫ j) (i ≫ j) = pullback.fst a i :=
  (conductorSquare a j i).isoPullback_hom_fst

theorem conductorIso_hom_snd :
    (conductorIso a j i).hom ≫ pullback.snd (a ≫ j) (i ≫ j) = pullback.snd a i :=
  (conductorSquare a j i).isoPullback_hom_snd

variable (b : O ⟶ L) (hb : b ≫ n = i)

include hn hb in
theorem branch_over : (b ≫ e) ≫ p = i ≫ j := by
  rw [Category.assoc, hn.w, ← Category.assoc, hb]

/-- The two realizations of the base-changed branch are the same scheme morphism. -/
theorem branchIso_natural :
    (conductorIso a j i).hom ≫
      pullbackMap (a ≫ j) (b ≫ e) (branch_over j n e p hn i b hb) =
        pullbackMap a b hb ≫ (normIso a j n e p hn).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackMap_fst, conductorIso_hom_fst, Category.assoc,
      normIso_hom_fst, pullbackMap_fst]
  · rw [Category.assoc, pullbackMap_snd, ← Category.assoc, conductorIso_hom_snd,
      Category.assoc, normIso_hom_snd]
    simp only [Category.assoc, pullbackMap_snd_assoc]

end
end ManuscriptAudit.NormalizationBranchChartTransport

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NormalizationBranchChartTransport.normIso_hom_fst,
      ``ManuscriptAudit.NormalizationBranchChartTransport.conductorIso_hom_fst,
      ``ManuscriptAudit.NormalizationBranchChartTransport.branchIso_natural] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
