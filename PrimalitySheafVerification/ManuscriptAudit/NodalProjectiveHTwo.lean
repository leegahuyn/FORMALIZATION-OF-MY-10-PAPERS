import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleMayerVietorisSecondCokernel
import PrimalitySheafVerification.ManuscriptAudit.NodalAffineHigherCohomology
import PrimalitySheafVerification.ManuscriptAudit.NodalCompactSupportHigher
import PrimalitySheafVerification.ManuscriptAudit.NodalHigherChartCohomology
import PrimalitySheafVerification.ManuscriptAudit.NodalProjectiveKummerComparison

/-! Actual second-degree ordinary and compactly supported cohomology of the split nodal curve. -/

namespace ManuscriptAudit.NodalProjectiveHTwo

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open EtaleOpenIntersection (fstLeg sndLeg intersection_isPullback)
open NodalProjectiveClosure (affineNode affineOpen projectiveNode)
open NodalProperYChart (chartOpen)
open NodalYChartHOneCokernel (F)
open NodalYChartPrincipalOpen (principalObject principalRingHom overlapEtaleIso overlapEtaleIso_snd)
open NodalProjectiveKummerComparison (C chartCohomologyEquiv terminalCohomologyEquiv affine_leg_eq_zero)
open NodalCompactSupportHOne (nodalHc nodalHcHigherProjectiveEquiv)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (K : Type) [Field K] [IsAlgClosed K]

private abbrev overlap := EtaleOpenIntersection.intersection (affineOpen K) (chartOpen K)

private def toOverlap (d : ℕ) :
    (F K d).H' 1 (Scheme.Etale.mk (chartOpen K)) →+ (F K d).H' 1 (overlap K) :=
  (((F K d).cohomologyPresheaf 1).map (sndLeg (affineOpen K) (chartOpen K)).op).hom

private def overlapCokernelEquiv (d : ℕ) :
    (((F K d).H' 1 (overlap K) : Type) ⧸ (toOverlap K d).range) ≃+
      (((F K d).H' 1 (principalObject K) : Type) ⧸
        (NodalYChartHOneCokernel.restriction K d).range) := by
  let P := (F K d).cohomologyPresheaf 1
  let φ := overlapEtaleIso K
  let e := (P.mapIso φ.op).addCommGroupIsoToAddEquiv
  let a := KummerRelativeUnitSections.chartArrow (principalRingHom K) (chartOpen K)
  let i := NodalYChartHOneCokernel.restriction K d
  let r := toOverlap K d
  have h : e.toAddMonoidHom.comp i = r.comp (AddMonoidHom.id _) := by
    apply AddMonoidHom.ext
    intro x
    change P.map φ.hom.op (P.map a.op x) = P.map (sndLeg (affineOpen K) (chartOpen K)).op x
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, overlapEtaleIso_snd K]
  let e' := AdditiveCokernelPresentation.cokernelEquiv i (AddMonoidHom.id _) e.toAddMonoidHom r
    (fun x ↦ ⟨x, rfl⟩) e.surjective h
  have hKer : e.toAddMonoidHom.ker = ⊥ := AddMonoidHom.ker_eq_bot.mpr e.injective
  simpa only [hKer, sup_bot_eq] using e'

variable (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)]

/-- The actual second-degree proper nodal cohomology is the coefficient group. -/
def projectiveHTwoEquiv (h2 : (2 : K) ≠ 0) :
    Sheaf.H (C (projectiveNode K) ℓ) 2 ≃+ ZMod ℓ := by
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
  let G := F K ℓ
  have hA : Subsingleton (G.H' 2 S.X₂) :=
    ⟨fun x y ↦ (chartCohomologyEquiv K j ℓ 2).injective
      ((NodalAffineHigherCohomology.affine_H_add_two_subsingleton K h2 ℓ 0).elim _ _)⟩
  have hY : Subsingleton (G.H' 2 S.X₃) :=
    ⟨fun x y ↦ (chartCohomologyEquiv K k ℓ 2).injective
      ((NodalHigherChartCohomology.chart_H_add_two_subsingleton K ℓ 0).elim _ _)⟩
  let e : (((G.H' 1 (overlap K) : Type) ⧸ (toOverlap K ℓ).range)) ≃+ G.H' 2 S.X₄ :=
    EtaleMayerVietorisSecondCokernel.cokernelEquiv S G 1 (affine_leg_eq_zero K h2 ℓ) hA hY
  let hℓ := (Fact.out : ℓ.Prime).pos
  exact (terminalCohomologyEquiv K ℓ 2).symm.trans (e.symm.trans
    ((overlapCokernelEquiv K ℓ).trans (NodalYChartHOneCokernel.cokernelEquiv K ℓ hℓ)))

/-- The genuine compact-support H² of the affine nodal curve is one copy of the coefficient group. -/
def compactHTwoEquiv (h2 : (2 : K) ≠ 0) :
    nodalHc K (AddCommGrpCat.of (ZMod ℓ)) 2 ≃+ ZMod ℓ :=
  (nodalHcHigherProjectiveEquiv K (AddCommGrpCat.of (ZMod ℓ)) 0).trans
    (projectiveHTwoEquiv K ℓ h2)

end
end ManuscriptAudit.NodalProjectiveHTwo

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalProjectiveHTwo.projectiveHTwoEquiv,
      ``ManuscriptAudit.NodalProjectiveHTwo.compactHTwoEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
