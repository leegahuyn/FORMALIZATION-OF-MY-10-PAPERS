import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicClosedPairSupport
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicClosedRestrictionEpi
import PrimalitySheafVerification.ManuscriptAudit.ProetaleClosedSupportLocalConstants
import PrimalitySheafVerification.ManuscriptAudit.SheafProductSectionExt
import PrimalitySheafVerification.ManuscriptAudit.TwoOpenCokernelLift

/-! On disjoint closed supports, the native simultaneous continuous adic
restriction is epic on the actual pro-étale site. -/

namespace ManuscriptAudit.ProetaleAdicClosedPairEpi

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleContinuousDirectImageMaps (functions functionsOver diagonal)
open ProetaleClosedSupportLocalConstants (openObject openArrow)
open ProetaleAdicClosedPairSupport (boundary pairRestriction support inclusion)
open TwoOpenCokernelLift (coverObjects coverArrows)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X Z₀ Z₁ : Scheme.{0}} (i₀ : Z₀ ⟶ X) (i₁ : Z₁ ⟶ X)
variable [IsClosedImmersion i₀] [IsClosedImmersion i₁]
variable (ℓ : ℕ) [Fact ℓ.Prime]

private abbrev A := AddCommGrpCat.{1}
private abbrev M := ℤ_[ℓ]
private abbrev J := Scheme.ProEt.topology X
private abbrev G := boundary i₀ i₁ ℓ
private abbrev d := pairRestriction i₀ i₁ ℓ
private abbrev π₀ : G i₀ i₁ ℓ ⟶ functionsOver (M ℓ) i₀ := prod.fst
private abbrev π₁ : G i₀ i₁ ℓ ⟶ functionsOver (M ℓ) i₁ := prod.snd

private theorem section_eq_off_chart {Z : Scheme.{0}} {V : X.ProEt} (i : Z ⟶ X)
    (h : Disjoint (Set.range V.hom) (Set.range i))
    (s t : (functionsOver (M ℓ) i).obj.obj (op V)) : s = t := by
  apply ULift.ext
  apply ContinuousMap.ext
  intro x
  change ↥(pullback V.hom i : Scheme.{0}) at x
  have hx : V.hom (pullback.fst V.hom i x) = i (pullback.snd V.hom i x) :=
    congrArg (fun f : pullback V.hom i ⟶ X ↦ f x) (pullback.condition (f := V.hom) (g := i))
  exact (Set.disjoint_left.mp h ⟨_, rfl⟩ ⟨_, hx.symm⟩).elim

private theorem arrow_disjoint {V W : X.ProEt} (a : W ⟶ V) {Z : Scheme.{0}} {i : Z ⟶ X}
    (h : Disjoint (Set.range V.hom) (Set.range i)) :
    Disjoint (Set.range W.hom) (Set.range i) := by
  refine disjoint_of_subset_left ?_ h
  rintro _ ⟨x, rfl⟩
  exact ⟨a.left x, congrArg (fun f : W.left ⟶ X ↦ f x) a.w⟩

private theorem lift_first {V : X.ProEt}
    (s : (G i₀ i₁ ℓ).obj.obj (op V)) (h : Disjoint (Set.range V.hom) (Set.range i₁)) :
    Presheaf.imageSieve (d i₀ i₁ ℓ).hom s ∈ J (X := X) V := by
  let p := π₀ i₀ i₁ ℓ
  let t := p.hom.app (op V) s
  have hCover := (ProetaleAdicClosedRestrictionEpi.restriction_locallySurjective i₀ ℓ).imageSieve_mem t
  refine (J (X := X)).superset_covering ?_ hCover
  rintro W a ⟨b, hb⟩
  refine ⟨b, ?_⟩
  apply SheafProductSectionExt.section_ext
  · change ((d i₀ i₁ ℓ ≫ p).hom.app (op W)) b = p.hom.app (op W) ((G i₀ i₁ ℓ).obj.map a.op s)
    rw [show d i₀ i₁ ℓ ≫ p = diagonal (M ℓ) i₀ from prod.lift_fst _ _,
      NatTrans.naturality_apply p.hom a.op s]
    exact hb
  · exact section_eq_off_chart ℓ i₁ (arrow_disjoint a h) _ _

private theorem lift_second {V : X.ProEt}
    (s : (G i₀ i₁ ℓ).obj.obj (op V)) (h : Disjoint (Set.range V.hom) (Set.range i₀)) :
    Presheaf.imageSieve (d i₀ i₁ ℓ).hom s ∈ J (X := X) V := by
  let p := π₁ i₀ i₁ ℓ
  let t := p.hom.app (op V) s
  have hCover := (ProetaleAdicClosedRestrictionEpi.restriction_locallySurjective i₁ ℓ).imageSieve_mem t
  refine (J (X := X)).superset_covering ?_ hCover
  rintro W a ⟨b, hb⟩
  refine ⟨b, ?_⟩
  apply SheafProductSectionExt.section_ext
  · exact section_eq_off_chart ℓ i₀ (arrow_disjoint a h) _ _
  · change ((d i₀ i₁ ℓ ≫ p).hom.app (op W)) b = p.hom.app (op W) ((G i₀ i₁ ℓ).obj.map a.op s)
    rw [show d i₀ i₁ ℓ ≫ p = diagonal (M ℓ) i₁ from prod.lift_snd _ _,
      NatTrans.naturality_apply p.hom a.op s]
    exact hb

set_option maxHeartbeats 2800000 in
theorem pairRestriction_locallySurjective (hDisjoint : Disjoint (Set.range i₀) (Set.range i₁)) :
    Presheaf.IsLocallySurjective (J (X := X)) (d i₀ i₁ ℓ).hom where
  imageSieve_mem {U} s := by
    let O₀ : U.left.Opens := U.hom ⁻¹ᵁ ⟨(Set.range i₁)ᶜ, i₁.isClosedEmbedding.isClosed_range.isOpen_compl⟩
    let O₁ : U.left.Opens := U.hom ⁻¹ᵁ ⟨(Set.range i₀)ᶜ, i₀.isClosedEmbedding.isClosed_range.isOpen_compl⟩
    let V := coverObjects (openObject U O₀) (openObject U O₁)
    let a := coverArrows (openArrow U O₀) (openArrow U O₁)
    have hCover : Sieve.ofArrows V a ∈ J (X := X) U := by
      apply Precoverage.generate_mem_toGrothendieck
      change (Presieve.ofArrows V a).map (Scheme.ProEt.forget X ⋙ Over.forget X) ∈
        Scheme.proetalePrecoverage U.left
      rw [Presieve.map_ofArrows]
      apply Scheme.etalePrecoverage_le_proetalePrecoverage _
      apply (Scheme.ofArrows_mem_precoverage_iff @Etale).mpr
      constructor
      · intro x
        by_cases hx : U.hom x ∈ Set.range i₁
        · refine ⟨true, ⟨x, ?_⟩, rfl⟩
          intro h₀
          exact Set.disjoint_left.mp hDisjoint h₀ hx
        · exact ⟨false, ⟨x, hx⟩, rfl⟩
      · intro b
        cases b
        · exact inferInstanceAs (Etale O₀.ι)
        · exact inferInstanceAs (Etale O₁.ι)
    apply (J (X := X)).transitive hCover
    rintro W e ⟨_, b, _, ⟨k⟩, rfl⟩
    rw [Sieve.pullback_comp]
    apply (J (X := X)).pullback_stable b
    rw [Presheaf.pullback_imageSieve]
    cases k
    · apply lift_first i₀ i₁ ℓ
      exact Set.disjoint_left.mpr (by rintro _ ⟨x, rfl⟩ h; exact x.property h)
    · apply lift_second i₀ i₁ ℓ
      exact Set.disjoint_left.mpr (by rintro _ ⟨x, rfl⟩ h; exact x.property h)

theorem pairRestriction_epi (hDisjoint : Disjoint (Set.range i₀) (Set.range i₁)) :
    Epi (d i₀ i₁ ℓ) := by
  letI : Sheaf.IsLocallySurjective (d i₀ i₁ ℓ) := pairRestriction_locallySurjective i₀ i₁ ℓ hDisjoint
  exact Sheaf.epi_of_isLocallySurjective (d i₀ i₁ ℓ)

def sequence : ShortComplex (Sheaf (J (X := X)) A) :=
  ShortComplex.mk (inclusion i₀ i₁ ℓ) (d i₀ i₁ ℓ) (kernel.condition (d i₀ i₁ ℓ))

theorem sequence_shortExact (hDisjoint : Disjoint (Set.range i₀) (Set.range i₁)) :
    (sequence i₀ i₁ ℓ).ShortExact := by
  exact ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_f_is_kernel (sequence i₀ i₁ ℓ) (kernelIsKernel (d i₀ i₁ ℓ)))
    (inferInstanceAs (Mono (inclusion i₀ i₁ ℓ))) (pairRestriction_epi i₀ i₁ ℓ hDisjoint)

end
end ManuscriptAudit.ProetaleAdicClosedPairEpi

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleAdicClosedPairEpi.pairRestriction_epi,
      ``ManuscriptAudit.ProetaleAdicClosedPairEpi.sequence_shortExact] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
