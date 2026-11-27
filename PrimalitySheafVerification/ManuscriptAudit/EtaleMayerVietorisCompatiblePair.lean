import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleMayerVietorisNontrivial

/-! A pair of actual local degree-one étale classes with equal overlap
restrictions admits an ambient lift with both specified restrictions. -/

namespace ManuscriptAudit.EtaleMayerVietoris

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open ComposableArrows EtaleOpenIntersection EtaleTwoOpenHOne

noncomputable section

universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable {U V X : Scheme.{u}} (j : U ⟶ X) (k : V ⟶ X)
variable [IsOpenImmersion j] [IsOpenImmersion k]
variable (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
variable (hCover : Set.range j ∪ Set.range k = Set.univ)

include hCover in
/-- A pair of compatible chart classes lifts to an ambient class through
the genuine native Mayer–Vietoris exact sequence. -/
theorem existsHOne_of_compatible_pair
    (x : F.H' 1 (Scheme.Etale.mk j)) (y : F.H' 1 (Scheme.Etale.mk k))
    (h : (F.cohomologyPresheaf 1).map (fstLeg j k).op x =
         (F.cohomologyPresheaf 1).map (sndLeg j k).op y) :
    ∃ z : F.H' 1 (identityObject X),
      (F.cohomologyPresheaf 1).map (openArrow j).op z = x ∧
      (F.cohomologyPresheaf 1).map (openArrow k).op z = y := by
  let S := openCoverSquare j k (pullback.fst j k ≫ j) (fstLeg j k) (sndLeg j k)
    (intersection_isPullback j k) hCover
  let P := AddCommGrpCat.biprodIsoProd (F.H' 1 S.X₂) (F.H' 1 S.X₃)
  let w : ↑(F.H' 1 S.X₂ ⊞ F.H' 1 S.X₃) := P.inv ⟨x, y⟩
  have hw : w ∈ (S.fromBiprod F 1).hom.ker := by
    change S.fromBiprod F 1 (P.inv ⟨x, y⟩) = 0
    change S.fromBiprod F 1 ((AddCommGrpCat.biprodIsoProd _ _).inv ⟨x, y⟩) = 0
    rw [S.fromBiprod_biprodIsoProd_inv_apply]
    exact sub_eq_zero.mpr h
  have hExact : (S.toBiprod F 1).hom.range = (S.fromBiprod F 1).hom.ker :=
    ((S.sequence_exact F 0 1 rfl).exact' 3 4 5).ab_range_eq_ker
  rw [← hExact] at hw
  obtain ⟨z, hz⟩ := hw
  have he : P.hom (S.toBiprod F 1 z) = ⟨x, y⟩ := by
    have := congrArg (fun a : ↑(F.H' 1 S.X₂ ⊞ F.H' 1 S.X₃) => P.hom a) hz
    exact this.trans (P.inv_hom_id_apply _)
  rw [S.toBiprod_apply] at he
  have hp : ((F.cohomologyPresheaf 1).map S.f₂₄.op z,
      (F.cohomologyPresheaf 1).map S.f₃₄.op z) = (x, y) :=
    (P.inv_hom_id_apply _).symm.trans he
  exact ⟨z, congrArg Prod.fst hp, congrArg Prod.snd hp⟩

end
end ManuscriptAudit.EtaleMayerVietoris

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.EtaleMayerVietoris.existsHOne_of_compatible_pair
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
