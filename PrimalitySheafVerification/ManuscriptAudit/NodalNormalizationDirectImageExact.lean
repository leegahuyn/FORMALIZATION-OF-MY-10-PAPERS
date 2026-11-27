import Lean.Util.CollectAxioms
import Mathlib.Tactic.FinCases
import PrimalitySheafVerification.ManuscriptAudit.EtaleDirectImageRestrictionPullback
import PrimalitySheafVerification.ManuscriptAudit.EtaleSurjectiveRestriction
import PrimalitySheafVerification.ManuscriptAudit.EtaleTwoBranchDirectImage
import PrimalitySheafVerification.ManuscriptAudit.NodalNormalizationSwapRetraction
import PrimalitySheafVerification.ManuscriptAudit.SplitClosedEtaleDirectImage

/-! The actual finite affine nodal normalization has exact étale direct image. -/

namespace ManuscriptAudit.NodalNormalizationDirectImageExact

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NodalNormalizationFiber (B affineLine affineNode affineNormalization)
open NodalNormalizationSwapPullback (splitScheme first second toCover toLine)
open NodalNormalizationSwapRetraction (firstRetraction secondRetraction)
open NodalSwapCoverNoSection (coverScheme coverMap coverMap_etale coverMap_surjective)
open SmallEtaleBaseChange EtaleObjectRestriction

noncomputable section
universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type u) [Field K]

private def productFunctions : (B K × B K) ≃ₐ[B K] (Fin 2 → B K) :=
  { (RingEquiv.piFinTwo (fun _ : Fin 2 ↦ B K)).symm with
    commutes' := by
      intro b
      funext a
      fin_cases a <;> rfl }

private theorem toLine_etale : Etale (toLine K) :=
  (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr (Algebra.Etale.of_equiv (productFunctions K).symm))

private def branch (a : Bool) : affineLine K ⟶ splitScheme K :=
  if a then second K else first K

private theorem branch_over_line (a : Bool) :
    branch K a ≫ toLine K = 𝟙 (affineLine K) := by
  cases a <;> simp only [branch, Bool.false_eq_true, if_false, if_true, first, second, toLine]
  all_goals
    rw [← Spec.map_comp, ← Spec.map_id]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro b
    rfl

private theorem branch_etale (a : Bool) : Etale (branch K a) := by
  letI := toLine_etale K
  letI : Etale (branch K a ≫ toLine K) := by
    rw [branch_over_line]
    infer_instance
  exact Etale.of_comp (branch K a) (toLine K)

private theorem branch_mono (a : Bool) : Mono (branch K a) := by
  have h : branch K a ≫ toLine K = 𝟙 _ := branch_over_line K a
  exact mono_of_mono_fac h

private theorem branches_cover (x : splitScheme K) :
    ∃ (a : Bool) (y : affineLine K), (branch K a) y = x := by
  rcases NodalNormalizationSwapPullback.components_cover K x with ⟨y, hy⟩ | ⟨y, hy⟩
  · exact ⟨false, y, hy⟩
  · exact ⟨true, y, hy⟩

private theorem first_second_disjoint :
    Disjoint (Set.range (first K)) (Set.range (second K)) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
  change PrimeSpectrum.comap (RingHom.snd (B K) (B K)) y =
    PrimeSpectrum.comap (RingHom.fst (B K) (B K)) x at hy
  let e := PrimeSpectrum.primeSpectrumProd (B K) (B K)
  have h : e.symm (Sum.inl x) = e.symm (Sum.inr y) :=
    (PrimeSpectrum.primeSpectrumProd_symm_inl x).trans
      (hy.symm.trans (PrimeSpectrum.primeSpectrumProd_symm_inr y).symm)
  exact Sum.inl_ne_inr (e.symm.injective h)

private theorem branches_disjoint (a b : Bool) (hab : a ≠ b) :
    Disjoint (Set.range (branch K a)) (Set.range (branch K b)) := by
  cases a <;> cases b
  · exact (hab rfl).elim
  · exact first_second_disjoint K
  · exact (first_second_disjoint K).symm
  · exact (hab rfl).elim

private def retraction (a : Bool) : coverScheme K ⟶ affineLine K :=
  if a then secondRetraction K else firstRetraction K

private theorem branch_closed (h2 : (2 : K) ≠ 0) (a : Bool) :
    IsClosedImmersion (branch K a ≫ toCover K) := by
  cases a
  · exact NodalNormalizationSwapPullback.first_closed K h2
  · exact NodalNormalizationSwapPullback.second_closed K h2

private theorem branch_split (a : Bool) :
    (branch K a ≫ toCover K) ≫ retraction K a = 𝟙 (affineLine K) := by
  cases a
  · exact NodalNormalizationSwapRetraction.first_retraction K
  · exact NodalNormalizationSwapRetraction.second_retraction K

set_option maxHeartbeats 2000000 in
/-- The direct image of any epi along the native affine nodal normalization is epi. -/
theorem map_epi (h2 : (2 : K) ≠ 0)
    {F G : Sheaf (affineLine K).smallEtaleTopology AddCommGrpCat.{u}} (α : F ⟶ G) [Epi α] :
    Epi ((directImage (affineNormalization K) AddCommGrpCat.{u}).map α) := by
  let A := AddCommGrpCat.{u}
  let f := affineNormalization K
  let j := coverMap K
  let p := toLine K
  let q := toCover K
  letI : Etale j := coverMap_etale K h2
  letI : Etale p := toLine_etale K
  letI : ∀ a, Etale (branch K a) := branch_etale K
  letI : ∀ a, Mono (branch K a) := branch_mono K
  letI : (restriction p).IsLeftAdjoint := (restrictionAdjunction p).isLeftAdjoint
  let β := (restriction p).map α
  letI : Epi β := (restriction p).map_epi α
  have hBranch (a : Bool) :
      Epi ((directImage (branch K a ≫ q) A).map ((restriction (branch K a)).map β)) := by
    let i := branch K a
    letI : (restriction i).IsLeftAdjoint := (restrictionAdjunction i).isLeftAdjoint
    letI : Epi ((restriction i).map β) := (restriction i).map_epi β
    letI : IsClosedImmersion (i ≫ q) := branch_closed K h2 a
    exact SplitClosedEtaleDirectImage.map_epi (i ≫ q) (retraction K a)
      (branch_split K a) ((restriction i).map β)
  haveI : Epi ((directImage q A).map β) :=
    EtaleTwoBranchDirectImage.map_epi_of_branches q (branch K) (branches_cover K)
      (branches_disjoint K) β hBranch
  let e := EtaleDirectImageRestrictionPullback.directImageRestrictionIso
    (NodalNormalizationSwapPullback.split_isPullback K h2).flip
  let mapF := ((directImage f A) ⋙ restriction j).map α
  have hEpi : Epi mapF := by
    apply (epi_comp_iff_of_isIso mapF (e.hom.app G)).mp
    change Epi (((directImage f A ⋙ restriction j).map α) ≫ e.hom.app G)
    rw [e.hom.naturality α]
    exact inferInstanceAs (Epi (e.hom.app F ≫ (directImage q A).map β))
  letI : Epi ((restriction j).map ((directImage f A).map α)) := hEpi
  exact EtaleSurjectiveRestriction.epi_of_restriction_epi j (coverMap_surjective K h2) _

end
end ManuscriptAudit.NodalNormalizationDirectImageExact

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NodalNormalizationDirectImageExact.map_epi
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
