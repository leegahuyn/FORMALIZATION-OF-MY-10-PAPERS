import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalNormalizationEtaleFibers

/-! The conductor difference of the two branches has the actual
constant sheaf as its kernel on the affine split node. -/

namespace ManuscriptAudit.NodalConductorSheafKernel

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open EtaleContinuousMapSheaf EtaleContinuousDirectImageMaps
open NodalNormalizationFiber (affineNode affineNormalization affineNormalization_finite
  affineNormalization_surjective)
open NodalNormalizationEtaleFibers (Norm Conductor plus minus points_equal_off_conductor
  point_lifts_to_branch conductor_projection_injective)
open NodalNormalizationBranches (branchMap plus_over_node minus_over_node)
open NodalAffineOrigin (originMap originPoint)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (K : Type u) [Field K]
variable (M : AddCommGrpCat.{u}) [TopologicalSpace M] [DiscreteTopology M]
variable [IsTopologicalAddGroup M]

abbrev baseFunctions := continuousMapSheaf (affineNode K) M
abbrev normalizationFunctions := functionsOver M (affineNormalization K)
abbrev conductorFunctions := functionsOver M (originMap K)

abbrev baseDiagonal : baseFunctions K M ⟶ normalizationFunctions K M :=
  diagonal M (affineNormalization K)

/-- The actual two branch restrictions of normalization functions, with
the ordered difference. -/
def branchDifference : normalizationFunctions K M ⟶ conductorFunctions K M :=
  restriction M (branchMap K 1) (plus_over_node K) -
    restriction M (branchMap K (-1)) (minus_over_node K)

theorem diagonal_difference_zero : baseDiagonal K M ≫ branchDifference K M = 0 := by
  unfold branchDifference
  rw [Preadditive.comp_sub, diagonal_restriction, diagonal_restriction, sub_self]

abbrev UOver := (affineNode K).Etale

private abbrev projection (U : UOver K) := pullback.fst U.hom (affineNormalization K)

private theorem projection_surjective (h2 : (2 : K) ≠ 0) (U : UOver K) :
    Function.Surjective (projection K U) := by
  intro y
  obtain ⟨b, hb⟩ := affineNormalization_surjective K h2 (U.hom y)
  obtain ⟨t, ht, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := U.hom) (g := affineNormalization K) y b hb.symm
  exact ⟨t, ht⟩

private theorem projection_quotient (h2 : (2 : K) ≠ 0) (U : UOver K) :
    Topology.IsQuotientMap (projection K U) := by
  letI : IsFinite (affineNormalization K) := affineNormalization_finite K h2
  exact (projection K U).isClosedMap.isQuotientMap (projection K U).continuous
    (projection_surjective K h2 U)

private theorem plus_projection (U : UOver K) (c : (Conductor K U).left) :
    projection K U (plus K U c) = pullback.fst U.hom (originMap K) c := by
  change (plus K U ≫ projection K U) c = _
  unfold plus
  rw [baseChangeMap_fst]

private theorem minus_projection (U : UOver K) (c : (Conductor K U).left) :
    projection K U (minus K U c) = pullback.fst U.hom (originMap K) c := by
  change (minus K U ≫ projection K U) c = _
  unfold minus
  rw [baseChangeMap_fst]

private theorem sameOnFibers (U : UOver K) (s : ContinuousMap (Norm K U).left M)
    (hs : ∀ c : (Conductor K U).left, s (plus K U c) = s (minus K U c)) :
    Function.FactorsThrough s (projection K U) := by
  intro a b hab
  let y := projection K U a
  by_cases hy : U.hom y = originPoint K
  · have liftBranch (t : (Norm K U).left) (ht : projection K U t = y) :
        ∃ c : (Conductor K U).left, (plus K U c = t ∨ minus K U c = t) ∧
          pullback.fst U.hom (originMap K) c = y := by
      have ht' : U.hom (projection K U t) = originPoint K := by rw [ht]; exact hy
      rcases point_lifts_to_branch K U t ht' with ⟨c, hc⟩ | ⟨c, hc⟩
      · exact ⟨c, Or.inl hc, (plus_projection K U c).symm.trans ((congrArg (projection K U) hc).trans ht)⟩
      · exact ⟨c, Or.inr hc, (minus_projection K U c).symm.trans ((congrArg (projection K U) hc).trans ht)⟩
    obtain ⟨c, hc, hcp⟩ := liftBranch a rfl
    obtain ⟨d, hd, hdp⟩ := liftBranch b hab.symm
    have he : c = d := conductor_projection_injective K U (hcp.trans hdp.symm)
    subst d
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
    · rfl
    · exact hs c
    · exact (hs c).symm
    · rfl
  · exact congrArg s (points_equal_off_conductor K U a b y hy rfl hab.symm)

/-- A pulled-back function is uniquely determined by the original function. -/
theorem diagonal_injective_on_sections (h2 : (2 : K) ≠ 0) (U : UOver K) :
    Function.Injective ((baseDiagonal K M).hom.app (op U)) := by
  intro a b h
  apply ContinuousMap.ext
  intro y
  obtain ⟨t, ht⟩ := projection_surjective K h2 U y
  let a' : ContinuousMap U.left M := a
  let b' : ContinuousMap U.left M := b
  have he := congrArg (fun f : ContinuousMap (Norm K U).left M => f t) h
  change a' (projection K U t) = b' (projection K U t) at he
  change a' y = b' y
  rwa [ht] at he

/-- The full small-étale pointwise kernel of the actual branch difference
is precisely pullback of continuous functions on the nodal base. -/
theorem exact_on_sections (h2 : (2 : K) ≠ 0) (U : UOver K) :
    Function.Exact ((baseDiagonal K M).hom.app (op U)) ((branchDifference K M).hom.app (op U)) := by
  intro s
  constructor
  · intro hs
    let s' : ContinuousMap (Norm K U).left M := s
    have hbal (c : (Conductor K U).left) : s' (plus K U c) = s' (minus K U c) := by
      have hh := congrArg (fun t : ContinuousMap (Conductor K U).left M => t c) hs
      change s' (plus K U c) - s' (minus K U c) = 0 at hh
      exact sub_eq_zero.mp hh
    let p : ContinuousMap (Norm K U).left U.left := ⟨projection K U, (projection K U).continuous⟩
    have hp : Topology.IsQuotientMap p := projection_quotient K h2 U
    have hf : Function.FactorsThrough s' p := sameOnFibers K M U s' hbal
    refine ⟨hp.lift s' hf, ?_⟩
    change (hp.lift s' hf).comp p = s'
    exact hp.lift_comp s' hf
  · rintro ⟨s, rfl⟩
    have h := ConcreteCategory.congr_hom (congrArg (fun f =>
      f.hom.app (op U)) (diagonal_difference_zero K M)) s
    exact h

end
end ManuscriptAudit.NodalConductorSheafKernel

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalConductorSheafKernel.diagonal_difference_zero,
      ``ManuscriptAudit.NodalConductorSheafKernel.diagonal_injective_on_sections,
      ``ManuscriptAudit.NodalConductorSheafKernel.exact_on_sections] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
