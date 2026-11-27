import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalIntegralGluing

/-! The two charts are a cover of the integral glued model. Their
specified overlap is their actual scheme pullback. -/

namespace ManuscriptAudit.NodalIntegralGluingOverlap

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NodalIntegralGluing

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (R : Type u) [CommRing R]

theorem overlapToZ_chartIn :
    overlapToZ R ≫ chartIn R false = colimit.ι (diagram R) none :=
  colimit.w (diagram R) (WidePushoutShape.Hom.init false)

theorem overlapToY_chartIn :
    overlapToY R ≫ chartIn R true = colimit.ι (diagram R) none :=
  colimit.w (diagram R) (WidePushoutShape.Hom.init true)

theorem overlap_condition :
    overlapToZ R ≫ chartIn R false = overlapToY R ≫ chartIn R true :=
  (overlapToZ_chartIn R).trans (overlapToY_chartIn R).symm

theorem charts_cover (p : model R) :
    p ∈ Set.range (chartIn R false) ∨ p ∈ Set.range (chartIn R true) := by
  obtain ⟨i, q, hq⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (diagram R) p
  cases i with
  | none =>
    left
    refine ⟨overlapToZ R q, ?_⟩
    rw [← Scheme.Hom.comp_apply, overlapToZ_chartIn]
    exact hq
  | some b =>
    cases b
    · exact Or.inl ⟨q, hq⟩
    · exact Or.inr ⟨q, hq⟩

private theorem overlap_range :
    Set.range (overlapToZ R) =
      Set.range (pullback.fst (chartIn R false) (chartIn R true)) := by
  rw [IsOpenImmersion.range_pullbackFst]
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨overlapToY R q, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, overlap_condition]
  · rintro ⟨q, hq⟩
    have h : colimit.ι (diagram R) (some false) p =
        colimit.ι (diagram R) (some true) q := hq.symm
    obtain ⟨i, f, g, x, hx, hy⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff (diagram R)).mp h
    cases f with
    | init _ => exact ⟨x, hx⟩
    | id _ => cases g

/-- The given transition of the glued nodal curve is the native
intersection of its charts. This description works over the integers. -/
theorem overlap_isPullback :
    IsPullback (overlapToZ R) (overlapToY R) (chartIn R false) (chartIn R true) := by
  let e := IsOpenImmersion.isoOfRangeEq (overlapToZ R) (pullback.fst
    (chartIn R false) (chartIn R true)) (overlap_range R)
  have hF : e.hom ≫ pullback.fst (chartIn R false) (chartIn R true) = overlapToZ R :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hS : e.hom ≫ pullback.snd (chartIn R false) (chartIn R true) = overlapToY R := by
    apply (cancel_mono (chartIn R true)).mp
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hF, overlap_condition]
  exact IsPullback.of_iso_pullback ⟨overlap_condition R⟩ e hF hS

end
end ManuscriptAudit.NodalIntegralGluingOverlap

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalIntegralGluingOverlap.charts_cover,
      ``ManuscriptAudit.NodalIntegralGluingOverlap.overlap_isPullback] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
