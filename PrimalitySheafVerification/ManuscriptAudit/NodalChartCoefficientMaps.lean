import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalChartCoefficientRingMaps

/-! The two actual affine coefficient squares of the nodal cubic are pullbacks. -/

namespace ManuscriptAudit.NodalChartCoefficientMaps

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
open NodalIntegralChartTransition

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 170000
set_option synthInstance.maxHeartbeats 14000

universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

private theorem cast_map_isPullback {p : Polynomial (Polynomial R)}
    {q : Polynomial (Polynomial S)} (h : PlaneEquationBaseChange.equation R S p = q) :
    IsPullback (PlaneEquationBaseChange.structureMap S q)
      (Spec.map (CommRingCat.ofHom ((rootRingCongr S h).toRingHom.comp
        (PlaneEquationBaseChange.ringMap R S p))))
      (PlaneEquationBaseChange.changeBase R S) (PlaneEquationBaseChange.structureMap R p) := by
  let e := Scheme.Spec.mapIso (rootRingCongr S h).toCommRingCatIso.op
  exact (PlaneEquationBaseChange.square_isPullback R S p).of_iso' e
    (.refl _) (.refl _) (.refl _)
    (by
      change Spec.map (CommRingCat.ofHom (rootRingCongr S h).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap S (AdjoinRoot (PlaneEquationBaseChange.equation R S p)))) =
        Spec.map (CommRingCat.ofHom (algebraMap S (AdjoinRoot q))) ≫ 𝟙 _
      rw [Category.comp_id, ← Spec.map_comp]
      apply congrArg Spec.map
      apply CommRingCat.hom_ext
      apply RingHom.ext
      exact (rootRingCongr S h).commutes)
    (by
      change Spec.map (CommRingCat.ofHom (rootRingCongr S h).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (PlaneEquationBaseChange.ringMap R S p)) =
        Spec.map (CommRingCat.ofHom ((rootRingCongr S h).toRingHom.comp
          (PlaneEquationBaseChange.ringMap R S p))) ≫ 𝟙 _
      rw [Category.comp_id, ← Spec.map_comp] <;> rfl)
    (by simp) (by simp)

theorem zSquare_isPullback :
    IsPullback (PlaneEquationBaseChange.structureMap S (zEquation S))
      (Spec.map (CommRingCat.ofHom (zRingMap R S))) (PlaneEquationBaseChange.changeBase R S)
      (PlaneEquationBaseChange.structureMap R (zEquation R)) :=
  cast_map_isPullback R S (zEquation_map R S)

theorem ySquare_isPullback :
    IsPullback (PlaneEquationBaseChange.structureMap S (yEquation S))
      (Spec.map (CommRingCat.ofHom (yRingMap R S))) (PlaneEquationBaseChange.changeBase R S)
      (PlaneEquationBaseChange.structureMap R (yEquation R)) :=
  cast_map_isPullback R S (yEquation_map R S)

end
end ManuscriptAudit.NodalChartCoefficientMaps

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalChartCoefficientMaps.zSquare_isPullback,
      ``ManuscriptAudit.NodalChartCoefficientMaps.ySquare_isPullback] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
