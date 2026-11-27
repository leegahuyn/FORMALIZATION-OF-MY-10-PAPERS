import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalProjectiveCyclicHOne
import PrimalitySheafVerification.ManuscriptAudit.NodalProjectiveHTwo

/-! Actual proper nodal degree-two cohomology for every invertible cyclic order. -/

namespace ManuscriptAudit.NodalProjectiveCyclicHTwo

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open NodalProjectiveClosure (affineOpen projectiveNode)
open NodalProperYChart (chartOpen)
open NodalYChartHOneCokernel (F)
open NodalProjectiveKummerComparison (C comparison chartCohomologyEquiv terminalCohomologyEquiv)
open EtaleOpenIntersection (fstLeg sndLeg intersection_isPullback)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (K : Type) [Field K] [IsAlgClosed K]
variable (d : ℕ) [NeZero (d : K)]

/-- The actual Kummer affine leg vanishes for any invertible cyclic coefficient order. -/
theorem affine_leg_eq_zero (h2 : (2 : K) ≠ 0) :
    (((F K d).cohomologyPresheaf 1).map (fstLeg (affineOpen K) (chartOpen K)).op).hom = 0 := by
  let a := fstLeg (affineOpen K) (chartOpen K)
  let P := (C (projectiveNode K) d).cohomologyPresheaf 1
  let Q := (F K d).cohomologyPresheaf 1
  let e := (Sheaf.cohomologyPresheafFunctor (projectiveNode K).smallEtaleTopology 1).mapIso
    (comparison K d)
  have hConst : P.map a.op = 0 := by
    apply ConcreteCategory.hom_ext
    intro x
    exact DFunLike.congr_fun (NodalProjectiveCyclicHOne.affine_leg_eq_zero K d h2) x
  have hn : P.map a.op ≫ e.hom.app (op (EtaleOpenIntersection.intersection (affineOpen K) (chartOpen K))) =
      e.hom.app (op (Scheme.Etale.mk (affineOpen K))) ≫ Q.map a.op :=
    e.hom.naturality a.op
  have hMap : Q.map a.op = 0 := by
    apply (cancel_epi (e.hom.app (op (Scheme.Etale.mk (affineOpen K))))).mp
    rw [← hn, hConst, zero_comp, comp_zero]
  exact congrArg (fun g ↦ g.hom) hMap

/-- The actual proper nodal H² is the coefficient group, via the native overlap cokernel. -/
def projectiveHTwoEquiv (h2 : (2 : K) ≠ 0) :
    Sheaf.H (C (projectiveNode K) d) 2 ≃+ ZMod d := by
  let j := affineOpen K
  let k := chartOpen K
  let l := pullback.fst j k ≫ j
  letI : IsOpenImmersion l := inferInstanceAs (IsOpenImmersion (pullback.fst j k ≫ j))
  let a := fstLeg j k
  let b := sndLeg j k
  let hD := intersection_isPullback j k
  have hCover : Set.range j ∪ Set.range k = Set.univ :=
    congrArg (fun O : (projectiveNode K).Opens ↦ (O : Set (projectiveNode K)))
      (NodalChartIntersection.charts_cover K)
  let S := EtaleMayerVietoris.openCoverSquare j k l a b hD hCover
  let M := F K d
  have hA : Subsingleton (M.H' 2 S.X₂) :=
    ⟨fun x y ↦ (chartCohomologyEquiv K j d 2).injective
      ((NodalAffineHigherCohomology.affine_H_add_two_subsingleton K h2 d 0).elim _ _)⟩
  have hY : Subsingleton (M.H' 2 S.X₃) :=
    ⟨fun x y ↦ (chartCohomologyEquiv K k d 2).injective
      ((NodalHigherChartCohomology.chart_H_add_two_subsingleton K d 0).elim _ _)⟩
  let r := ((M.cohomologyPresheaf 1).map b.op).hom
  let e : (((M.H' 1 (EtaleOpenIntersection.intersection j k) : Type) ⧸ r.range)) ≃+ M.H' 2 S.X₄ :=
    EtaleMayerVietorisSecondCokernel.cokernelEquiv S M 1 (affine_leg_eq_zero K d h2) hA hY
  letI : NeZero d := NeZero.of_neZero_natCast K
  let hd := Nat.pos_of_ne_zero (NeZero.ne d)
  exact (terminalCohomologyEquiv K d 2).symm.trans
    (e.symm.trans (NodalProjectiveHTwo.overlapCyclicCokernelEquiv K d hd))

end
end ManuscriptAudit.NodalProjectiveCyclicHTwo

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalProjectiveCyclicHTwo.affine_leg_eq_zero,
      ``ManuscriptAudit.NodalProjectiveCyclicHTwo.projectiveHTwoEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
