import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalChartIntersection
import PrimalitySheafVerification.ManuscriptAudit.PrincipalOpenEtaleAcyclic
import PrimalitySheafVerification.ManuscriptAudit.SchemeIsoSmallEtaleCohomology

/-! The actual Y chart and overlap of the proper nodal curve have no cyclic étale cohomology in degree at least two. -/

namespace ManuscriptAudit.NodalHigherChartCohomology

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NodalProjectiveClosure (affineOpen)
open NodalProperYChart (chartOpen)
open NodalYChartImmersion (nodeYChart coordinateEquiv)
open SmallEtaleEquivalenceCohomology
open Polynomial

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (K : Type) [Field K] [IsAlgClosed K]

private abbrev C (X : Scheme.{0}) (d : ℕ) :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ZMod d))

private abbrev denominator : K[X] := 1 - X ^ 2

private theorem denominator_ne_zero : denominator K ≠ 0 := by
  intro h
  exact (one_ne_zero : (1 : K) ≠ 0)
    (by simpa [denominator] using congrArg (Polynomial.eval (0 : K)) h)

private theorem overlap_denominator_ne_zero : NodalConductor.y K ≠ 0 := by
  have hx : NodalConductor.x K ≠ 0 := by
    intro h
    exact (neg_ne_zero.mpr (one_ne_zero : (1 : K) ≠ 0))
      (by simpa [NodalConductor.x] using congrArg (Polynomial.eval (0 : K)) h)
  exact mul_ne_zero hx Polynomial.X_ne_zero

/-- The genuine Y chart is the polynomial localization at its explicit denominator. -/
def chartIso : nodeYChart K ≅ PrincipalOpenEtaleAcyclic.U K (denominator K) :=
  (Scheme.Spec.mapIso (coordinateEquiv K).toRingEquiv.toCommRingCatIso.op).symm

/-- Vanishing on the native Y chart in every degree at least two. -/
theorem chart_H_add_two_subsingleton (d : ℕ) [NeZero (d : K)] (n : ℕ) :
    Subsingleton (Sheaf.H (C (nodeYChart K) d) (n + 2)) := by
  let e := schemeIsoCohomologyEquiv (chartIso K) (AddCommGrpCat.of (ZMod d)) (n + 2)
  have h := PrincipalOpenEtaleAcyclic.cyclic_H_add_two_subsingleton K (denominator K)
    (denominator_ne_zero K) d n
  exact ⟨fun a b ↦ e.injective (h.elim _ _)⟩

/-- Vanishing on the genuine scheme-theoretic chart intersection in every degree at least two. -/
theorem overlap_H_add_two_subsingleton (d : ℕ) [NeZero (d : K)] (n : ℕ) :
    Subsingleton (Sheaf.H (C (pullback (affineOpen K) (chartOpen K)) d) (n + 2)) := by
  let e := schemeIsoCohomologyEquiv (NodalChartIntersection.intersectionIsoParameter K)
    (AddCommGrpCat.of (ZMod d)) (n + 2)
  have h := PrincipalOpenEtaleAcyclic.cyclic_H_add_two_subsingleton K (NodalConductor.y K)
    (overlap_denominator_ne_zero K) d n
  exact ⟨fun a b ↦ e.injective (h.elim _ _)⟩

end
end ManuscriptAudit.NodalHigherChartCohomology

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalHigherChartCohomology.chartIso,
      ``ManuscriptAudit.NodalHigherChartCohomology.chart_H_add_two_subsingleton,
      ``ManuscriptAudit.NodalHigherChartCohomology.overlap_H_add_two_subsingleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
