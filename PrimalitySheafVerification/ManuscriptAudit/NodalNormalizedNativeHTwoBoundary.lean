import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.PrincipalOpenNativeResidueHTwo
import PrimalitySheafVerification.ManuscriptAudit.AffineLineNativeResidueHTwo
import PrimalitySheafVerification.ManuscriptAudit.NodalNormalizedNativeCharts
import PrimalitySheafVerification.ManuscriptAudit.NodalHigherChartCohomology
import PrimalitySheafVerification.ManuscriptAudit.ProetaleMayerVietorisConnecting
import PrimalitySheafVerification.ManuscriptAudit.SchemeIsoProetaleCohomology

/-! Both actual charts of the normalized node have zero finite native
degree-two cohomology. Its actual overlap boundary therefore surjects. -/

namespace ManuscriptAudit.NodalNormalizedNativeHTwoBoundary

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ProetaleAdicHOneDetection (finiteCoefficient)
open ProetaleOpenLocalLifts (openObject openArrow)
open ProetaleClosedOpenRestriction (restrictionFunctionsIso)
open ProetaleCohomologyIso (cohomologyIso)
open ProetaleMayerVietorisConnecting (connecting connecting_surjective)
open NodalProjectiveClosure (affineOpen)
open NodalProperYChart (chartOpen)
open NodalProjectiveNormalization (normalizedNode normalizationMap)
open NodalNormalizedNativeCharts (yToNormalized zToNormalized overlapToZ overlap_isPullback
  yToNormalized_isPullback zToNormalized_isPullback)
open NodalYChartImmersion (nodeYChart)
open NodalYChartOverlap (overlapRing)
open NodalYChartPrincipalOpen (principalInclusion)
open Polynomial

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K]

private abbrev A := AddCommGrpCat.{1}
private abbrev X := normalizedNode K
private abbrev Y := nodeYChart K
private abbrev Z := Spec (CommRingCat.of (Polynomial K))
private abbrev W := Spec (CommRingCat.of (overlapRing K))
private abbrev j := yToNormalized K
private abbrev k (h₂ : (2 : K) ≠ 0) := zToNormalized K h₂

private theorem range_fst {D X Y S : Scheme.{0}} {u : D ⟶ X} {v : D ⟶ Y}
    {f : X ⟶ S} {g : Y ⟶ S} (h : IsPullback u v f g) :
    Set.range u = f ⁻¹' Set.range g := by
  let e := h.isoPullback
  have he : e.hom ≫ pullback.fst f g = u := h.isoPullback_hom_fst
  have hi : e.inv ≫ u = pullback.fst f g := calc
    _ = e.inv ≫ e.hom ≫ pullback.fst f g :=
      congrArg (fun a : D ⟶ X ↦ e.inv ≫ a) he.symm
    _ = _ := e.inv_hom_id_assoc _
  calc
    _ = Set.range (pullback.fst f g) := by
      ext x
      constructor
      · rintro ⟨d, rfl⟩
        exact ⟨e.hom d, by rw [← Scheme.Hom.comp_apply, he]⟩
      · rintro ⟨d, rfl⟩
        exact ⟨e.inv d, by rw [← Scheme.Hom.comp_apply, hi]⟩
    _ = _ := Scheme.Pullback.range_fst f g

/-- The actual normalization charts cover the full normalized curve. -/
theorem cover (h₂ : (2 : K) ≠ 0) :
    Set.range (j K) ∪ Set.range (k K h₂) = Set.univ := by
  have hBase : Set.range (affineOpen K) ∪ Set.range (chartOpen K) = Set.univ :=
    congrArg (fun O : (NodalProjectiveClosure.projectiveNode K).Opens ↦
      (O : Set (NodalProjectiveClosure.projectiveNode K))) (NodalChartIntersection.charts_cover K)
  rw [range_fst (yToNormalized_isPullback K), range_fst (zToNormalized_isPullback K h₂),
    ← Set.preimage_union, Set.union_comm (Set.range (chartOpen K)), hBase, Set.preimage_univ]

variable (h₂ : (2 : K) ≠ 0)

abbrev overlapOpen : W K ⟶ X K := principalInclusion K ≫ j K

abbrev firstLeg : openObject (overlapOpen K) ⟶ openObject (j K) :=
  MorphismProperty.Over.homMk (principalInclusion K) (by
    simp only [openObject, Category.id_comp] <;> rfl)

abbrev secondLeg : openObject (overlapOpen K) ⟶ openObject (k K h₂) :=
  MorphismProperty.Over.homMk (overlapToZ K h₂) (by
    change overlapToZ K h₂ ≫ (𝟙 (Z K) ≫ k K h₂) =
      𝟙 (W K) ≫ overlapOpen K
    simpa only [Category.id_comp] using (overlap_isPullback K h₂).w.symm)

theorem overlap :
    IsPullback (firstLeg K) (secondLeg K h₂) (openArrow (j K)) (openArrow (k K h₂)) :=
  ProetaleAffineTensor.underlying_isPullback (overlap_isPullback K h₂)

variable (l r : ℕ) [Fact l.Prime] [NeZero ((l ^ r : ℕ) : K)]

local instance residueTopology (d : ℕ) : TopologicalSpace (ZMod d) := ⊥
local instance residueDiscrete (d : ℕ) : DiscreteTopology (ZMod d) := ⟨rfl⟩

private theorem denominator_ne_zero : (1 - Polynomial.X ^ 2 : Polynomial K) ≠ 0 := by
  intro h
  exact (one_ne_zero : (1 : K) ≠ 0)
    (by simpa using congrArg (Polynomial.eval (0 : K)) h)

set_option maxHeartbeats 4400000 in
/-- Actual native degree two on the original Y chart is zero. -/
theorem y_HTwo_subsingleton : Subsingleton (Sheaf.H (finiteCoefficient (Y K) l r) 2) := by
  let E := SchemeIsoProetaleCohomology.continuousCohomologyEquiv
    (NodalHigherChartCohomology.chartIso K) (ZMod (l ^ r)) 2
  have h := PrincipalOpenNativeResidueHTwo.native_HTwo_subsingleton K
    (1 - Polynomial.X ^ 2) (denominator_ne_zero K) l r
  exact ⟨fun a b ↦ E.injective (h.elim (E a) (E b))⟩

private def restrictionEquiv {U : Scheme.{0}} (u : U ⟶ X K) [IsOpenImmersion u] :
    Sheaf.H ((OpenProetaleExtension.restriction u A).obj (finiteCoefficient (X K) l r)) 2 ≃+
      Sheaf.H (finiteCoefficient U l r) 2 :=
  cohomologyIso (X := U) (restrictionFunctionsIso u (ZMod (l ^ r))) 2

set_option maxHeartbeats 4300000 in
/-- Every normalized projective residue class in degree two is a true Mayer–Vietoris boundary. -/
theorem boundary_surjective :
    Function.Surjective
      (connecting (j K) (k K h₂) (overlapOpen K) (firstLeg K) (secondLeg K h₂)
        (overlap K h₂) (cover K h₂) (finiteCoefficient (X K) l r) 1) := by
  letI := y_HTwo_subsingleton K l r
  letI := AffineLineNativeResidueHTwo.native_residue_HTwo_subsingleton K l r
  exact connecting_surjective (j K) (k K h₂) (overlapOpen K) (firstLeg K) (secondLeg K h₂)
    (overlap K h₂) (cover K h₂) (finiteCoefficient (X K) l r) 1
    (restrictionEquiv K l r (j K)).injective.subsingleton
    (restrictionEquiv K l r (k K h₂)).injective.subsingleton

end
end ManuscriptAudit.NodalNormalizedNativeHTwoBoundary

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalNormalizedNativeHTwoBoundary.y_HTwo_subsingleton,
      ``ManuscriptAudit.NodalNormalizedNativeHTwoBoundary.boundary_surjective] do
    let ax ← collectAxioms name
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
