import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.ShortComplex.Ab
import PrimalitySheafVerification.ManuscriptAudit.EtaleMayerVietorisOrdinary
import PrimalitySheafVerification.ManuscriptAudit.EtaleOpenIntersection

/-! A nonzero étale H¹ class on one chart whose overlap restriction
vanishes lifts to a nonzero ambient class by the actual
Mayer–Vietoris sequence. -/

namespace ManuscriptAudit.EtaleMayerVietoris

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open ComposableArrows EtaleOpenIntersection EtaleTwoOpenHOne

universe u

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable {U V X : Scheme.{u}} (j : U ⟶ X) (k : V ⟶ X)
variable [IsOpenImmersion j] [IsOpenImmersion k]
variable (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
variable (hCover : Set.range j ∪ Set.range k = Set.univ)

include hCover in
theorem existsHOne_of_overlap_zero (c : F.H' 1 (Scheme.Etale.mk j))
    (hc : (F.cohomologyPresheaf 1).map (fstLeg j k).op c = 0) :
    ∃ z : F.H' 1 (identityObject X), (F.cohomologyPresheaf 1).map (openArrow j).op z = c := by
  let S := openCoverSquare j k (pullback.fst j k ≫ j) (fstLeg j k) (sndLeg j k)
    (intersection_isPullback j k) hCover
  let i : F.H' 1 S.X₂ ⟶ F.H' 1 S.X₂ ⊞ F.H' 1 S.X₃ := biprod.inl
  let p : F.H' 1 S.X₂ ⊞ F.H' 1 S.X₃ ⟶ F.H' 1 S.X₂ := biprod.fst
  have hi : i ≫ S.fromBiprod F 1 = (F.cohomologyPresheaf 1).map (fstLeg j k).op := by
    exact biprod.inl_desc _ _
  have hb : S.toBiprod F 1 ≫ p = (F.cohomologyPresheaf 1).map (openArrow j).op := by
    exact biprod.lift_fst _ _
  have hp : i ≫ p = 𝟙 _ := biprod.inl_fst
  have hK : i c ∈ (S.fromBiprod F 1).hom.ker := by
    change S.fromBiprod F 1 (i c) = 0
    rw [← ConcreteCategory.comp_apply, hi]
    exact hc
  have hExact : (S.toBiprod F 1).hom.range = (S.fromBiprod F 1).hom.ker :=
    ((S.sequence_exact F 0 1 rfl).exact' 3 4 5).ab_range_eq_ker
  rw [← hExact] at hK
  obtain ⟨z, hz⟩ := hK
  refine ⟨z, ?_⟩
  have eq := congrArg (fun d => p d) hz
  change p (S.toBiprod F 1 z) = p (i c) at eq
  rw [← ConcreteCategory.comp_apply, hb, ← ConcreteCategory.comp_apply, hp] at eq
  change (F.cohomologyPresheaf 1).map (openArrow j).op z = c at eq
  exact eq

include hCover in
/-- A nonzero chart class with zero overlap restriction forces actual
ordinary degree-one ambient étale cohomology to be nontrivial. -/
theorem HOne_nontrivial_of_overlap_zero (c : F.H' 1 (Scheme.Etale.mk j)) (hne : c ≠ 0)
    (hc : (F.cohomologyPresheaf 1).map (fstLeg j k).op c = 0) :
    Nontrivial (Sheaf.H F 1) := by
  obtain ⟨z, hz⟩ := existsHOne_of_overlap_zero j k F hCover c hc
  have hnz : z ≠ 0 := by
    intro h
    rw [h, map_zero] at hz
    exact hne hz.symm
  let e := (terminalCohomologyIso F 1).addCommGroupIsoToAddEquiv
  exact ⟨⟨e z, 0, fun h => hnz (e.injective (h.trans (map_zero e).symm))⟩⟩

end
end ManuscriptAudit.EtaleMayerVietoris

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleMayerVietoris.existsHOne_of_overlap_zero,
      ``ManuscriptAudit.EtaleMayerVietoris.HOne_nontrivial_of_overlap_zero] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
