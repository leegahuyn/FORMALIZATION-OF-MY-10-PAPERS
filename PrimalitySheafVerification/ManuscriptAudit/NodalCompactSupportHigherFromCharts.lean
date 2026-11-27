import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleMayerVietorisConnecting
import PrimalitySheafVerification.ManuscriptAudit.EtaleOpenIntersection
import PrimalitySheafVerification.ManuscriptAudit.NodalCompactSupportHigher
import PrimalitySheafVerification.ManuscriptAudit.NodalHigherChartCohomology

/-! For the actual proper node, the two smooth terms leave only one affine-chart vanishing to prove in degree at least three. -/

namespace ManuscriptAudit.NodalCompactSupportHigherFromCharts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComposableArrows
open NodalProjectiveClosure (affineNode affineOpen projectiveNode)
open NodalProperYChart (chartOpen)
open NodalHigherChartCohomology NodalCompactSupportHOne
open OpenEtaleExtension

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (K : Type) [Field K] [IsAlgClosed K]

private abbrev A := AddCommGrpCat.{0}
private abbrev M (d : ℕ) : A := AddCommGrpCat.of (ZMod d)
private abbrev C (X : Scheme.{0}) (d : ℕ) :=
  (constantSheaf X.smallEtaleTopology A).obj (M d)

private def restrictedConstantEquiv {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]
    (d n : ℕ) :
    Sheaf.H ((restriction j A).obj (C X d)) n ≃+ Sheaf.H (C U d) n :=
  ((Sheaf.functorH U.smallEtaleTopology n).mapIso
    ((restrictionConstantIso j).app (M d))).addCommGroupIsoToAddEquiv

/-- In degree at least three, vanishing on the affine nodal chart implies vanishing on the proper node. -/
theorem projective_H_add_three_subsingleton (d : ℕ) [NeZero (d : K)] (n : ℕ)
    (hAffine : Subsingleton (Sheaf.H (C (affineNode K) d) (n + 3))) :
    Subsingleton (Sheaf.H (C (projectiveNode K) d) (n + 3)) := by
  let j := affineOpen K
  let k := chartOpen K
  let l := pullback.fst j k ≫ j
  letI : IsOpenImmersion l := inferInstanceAs (IsOpenImmersion (pullback.fst j k ≫ j))
  let a := EtaleOpenIntersection.fstLeg j k
  let b := EtaleOpenIntersection.sndLeg j k
  let hD := EtaleOpenIntersection.intersection_isPullback j k
  have hCover : Set.range j ∪ Set.range k = Set.univ :=
    congrArg (fun O : (projectiveNode K).Opens ↦ (O : Set (projectiveNode K)))
      (NodalChartIntersection.charts_cover K)
  let F := C (projectiveNode K) d
  let Q := EtaleMayerVietoris.ordinaryOpenCoverSequence j k l a b hD hCover F (n + 2)
  have hQ := EtaleMayerVietoris.ordinaryOpenCoverSequence_exact j k l a b hD hCover F (n + 2)
  have hU : Subsingleton (Sheaf.H ((restriction j A).obj F) (n + 3)) :=
    ⟨fun x y ↦ (restrictedConstantEquiv j d (n + 3)).injective (hAffine.elim _ _)⟩
  have hV : Subsingleton (Sheaf.H ((restriction k A).obj F) (n + 3)) :=
    ⟨fun x y ↦ (restrictedConstantEquiv k d (n + 3)).injective
      ((chart_H_add_two_subsingleton K d (n + 1)).elim _ _)⟩
  have hW : Subsingleton (Q.obj' 2) :=
    ⟨fun x y ↦ (restrictedConstantEquiv l d (n + 2)).injective
      ((overlap_H_add_two_subsingleton K d n).elim _ _)⟩
  have hCharts : Subsingleton (Q.obj' 4) := by
    let B₁ := AddCommGrpCat.of (Sheaf.H ((restriction j A).obj F) (n + 3))
    let B₂ := AddCommGrpCat.of (Sheaf.H ((restriction k A).obj F) (n + 3))
    let e := (AddCommGrpCat.biprodIsoProd B₁ B₂).addCommGroupIsoToAddEquiv
    exact ⟨fun x y ↦ e.injective (Prod.ext (hU.elim _ _) (hV.elim _ _))⟩
  have hSurj : Function.Surjective (Q.map' 2 3) := by
    intro x
    have hx : (Q.map' 3 4).hom x = 0 := hCharts.elim _ _
    have h := hQ.exact' 2 3 4
    rw [ShortComplex.ab_exact_iff_function_exact] at h
    exact (h x).mp hx
  exact ⟨fun x y ↦ by
    obtain ⟨x', rfl⟩ := hSurj x
    obtain ⟨y', rfl⟩ := hSurj y
    exact congrArg (Q.map' 2 3) (hW.elim x' y')⟩

/-- The genuine compact-support cohomology vanishes as soon as the corresponding affine nodal cohomology does. -/
theorem compact_H_add_three_subsingleton (d : ℕ) [NeZero (d : K)] (n : ℕ)
    (hAffine : Subsingleton (Sheaf.H (C (affineNode K) d) (n + 3))) :
    Subsingleton (nodalHc K (M d) (n + 3)) := by
  let e := nodalHcHigherProjectiveEquiv K (M d) (n + 1)
  have h := projective_H_add_three_subsingleton K d n hAffine
  exact ⟨fun x y ↦ e.injective (h.elim _ _)⟩

end
end ManuscriptAudit.NodalCompactSupportHigherFromCharts

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalCompactSupportHigherFromCharts.projective_H_add_three_subsingleton,
      ``ManuscriptAudit.NodalCompactSupportHigherFromCharts.compact_H_add_three_subsingleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
