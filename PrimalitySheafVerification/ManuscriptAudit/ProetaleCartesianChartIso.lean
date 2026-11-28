import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleBaseChange

/-! A literal cartesian scheme chart and its edges determine the native
pro-étale base-change isomorphisms. -/

namespace ManuscriptAudit.ProetaleCartesianChartIso

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ProetaleBaseChange (baseChange)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  {U₁ U₂ : X.ProEt} {V₁ V₂ : Y.ProEt}
  {g₁ : U₁.left ⟶ V₁.left} {g₂ : U₂.left ⟶ V₂.left}

/-- The actual chart isomorphism on the pro-étale slice. -/
def chartIso (H : IsPullback g₁ U₁.hom V₁.hom f) : (baseChange f).obj V₁ ≅ U₁ :=
  MorphismProperty.Over.isoMk H.isoPullback.symm H.isoPullback_inv_snd

private theorem map_fst (a : V₁ ⟶ V₂) :
    ((baseChange f).map a).left ≫ pullback.fst V₂.hom f =
      pullback.fst V₁.hom f ≫ a.left := by
  simp only [baseChange, MorphismProperty.Over.pullback_map_left, pullback.lift_fst]

private theorem map_snd (a : V₁ ⟶ V₂) :
    ((baseChange f).map a).left ≫ pullback.snd V₂.hom f = pullback.snd V₁.hom f := by
  simp only [baseChange, MorphismProperty.Over.pullback_map_left, pullback.lift_snd]

/-- Cartesian chart identifications commute with an actual edge. -/
theorem chartIso_naturality
    (H₁ : IsPullback g₁ U₁.hom V₁.hom f) (H₂ : IsPullback g₂ U₂.hom V₂.hom f)
    (a : V₁ ⟶ V₂) (b : U₁ ⟶ U₂) (h : b.left ≫ g₂ = g₁ ≫ a.left) :
    (chartIso f H₁).hom ≫ b = (baseChange f).map a ≫ (chartIso f H₂).hom := by
  have hi : (chartIso f H₁).inv ≫ (baseChange f).map a = b ≫ (chartIso f H₂).inv := by
    apply MorphismProperty.Over.Hom.ext
    change H₁.isoPullback.hom ≫ ((baseChange f).map a).left =
      b.left ≫ H₂.isoPullback.hom
    apply pullback.hom_ext
    · calc
        _ = H₁.isoPullback.hom ≫ (pullback.fst V₁.hom f ≫ a.left) := by
          rw [Category.assoc, map_fst]
        _ = g₁ ≫ a.left := by rw [← Category.assoc, H₁.isoPullback_hom_fst]
        _ = b.left ≫ g₂ := h.symm
        _ = _ := by rw [Category.assoc, H₂.isoPullback_hom_fst]
    · calc
        _ = H₁.isoPullback.hom ≫ pullback.snd V₁.hom f := by
          rw [Category.assoc, map_snd]
        _ = U₁.hom := H₁.isoPullback_hom_snd
        _ = b.left ≫ U₂.hom := (MorphismProperty.Over.w b).symm
        _ = _ := by rw [Category.assoc, H₂.isoPullback_hom_snd]
  apply (cancel_mono (chartIso f H₂).inv).mp
  calc
    _ = (chartIso f H₁).hom ≫ (b ≫ (chartIso f H₂).inv) := Category.assoc _ _ _
    _ = (baseChange f).map a := by rw [← hi, Iso.hom_inv_id_assoc]
    _ = _ := by rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end
end ManuscriptAudit.ProetaleCartesianChartIso

open Lean Elab Command in
run_cmd do
  let n := ``ManuscriptAudit.ProetaleCartesianChartIso.chartIso_naturality
  let ax ← collectAxioms n
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{n} depends on unexpected axioms {ax}"
  logInfo m!"{n} uses {ax}"
