import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleEpiLocalSurjectivity
import PrimalitySheafVerification.ManuscriptAudit.EtaleObjectRestriction

/-! Restriction to a surjective étale neighborhood detects epi maps of abelian sheaves. -/

namespace ManuscriptAudit.EtaleSurjectiveRestriction

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open SmallEtaleBaseChange EtaleObjectRestriction

noncomputable section
universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{u}

variable {Y X : Scheme.{u}} (j : Y ⟶ X) [Etale j] (hj : Function.Surjective j)

private theorem pullback_projection_surjective (U : X.Etale) :
    Function.Surjective (pullback.fst U.hom j) := by
  intro b
  obtain ⟨a, ha⟩ := hj (U.hom b)
  obtain ⟨c, hc, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := U.hom) (g := j) b a ha.symm
  exact ⟨c, hc⟩

/-- Étale restriction along a surjective scheme map detects local lifting for additive sheaves. -/
theorem locallySurjective_of_restriction
    {F G : Sheaf X.smallEtaleTopology A.{u}} (α : F ⟶ G)
    [Sheaf.IsLocallySurjective ((restriction j).map α)] :
    Sheaf.IsLocallySurjective α where
  imageSieve_mem {U} s := by
    let Z := (etaleBaseChange j).obj U
    let L := postcompose j
    let p : L.obj Z ⟶ U := MorphismProperty.Over.homMk (pullback.fst U.hom j)
      (pullback.condition (f := U.hom) (g := j))
    let s' := G.obj.map p.op s
    let R : Sieve Z := Presheaf.imageSieve ((restriction j).map α).hom s'
    have hR : R ∈ Y.smallEtaleTopology Z :=
      Presheaf.imageSieve_mem Y.smallEtaleTopology ((restriction j).map α).hom (U := op Z) s'
    obtain ⟨ι, W, g, he⟩ := Sieve.exists_eq_ofArrows R
    have hR' : Sieve.ofArrows W g ∈ Y.smallEtaleTopology Z := he ▸ hR
    have hCov := (Scheme.ofArrows_mem_smallEtaleTopology_iff g).mp hR'
    let a (k : ι) := L.map (g k) ≫ p
    have hCov' : Sieve.ofArrows (L.obj ∘ W) a ∈ X.smallEtaleTopology U := by
      rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
      apply Set.eq_univ_of_forall
      intro x
      obtain ⟨y, hy⟩ := pullback_projection_surjective j hj U x
      obtain ⟨k, z, hz⟩ := Set.mem_iUnion.mp ((Set.eq_univ_iff_forall.mp hCov) y)
      exact Set.mem_iUnion.mpr ⟨k, z, (congrArg (pullback.fst U.hom j) hz).trans hy⟩
    refine X.smallEtaleTopology.superset_covering ?_ hCov'
    apply (Sieve.generate_le_iff _ _).mpr
    rintro _ _ ⟨k⟩
    have hmem : R (g k) := he.symm ▸ Sieve.le_generate _ (Presieve.ofArrows.mk k)
    obtain ⟨b, hb⟩ := hmem
    refine ⟨b, ?_⟩
    change α.hom.app (op (L.obj (W k))) b = G.obj.map (a k).op s
    change α.hom.app (op (L.obj (W k))) b = G.obj.map (L.map (g k)).op s' at hb
    rw [a, op_comp, G.obj.map_comp, ConcreteCategory.comp_apply]
    exact hb

/-- Epimorphisms are reflected by restriction to a surjective étale cover. -/
theorem epi_of_restriction_epi {F G : Sheaf X.smallEtaleTopology A.{u}} (α : F ⟶ G)
    [Epi ((restriction j).map α)] : Epi α := by
  letI := EtaleEpiLocalSurjectivity.of_epi ((restriction j).map α)
  letI := locallySurjective_of_restriction j hj α
  infer_instance

end
end ManuscriptAudit.EtaleSurjectiveRestriction

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleSurjectiveRestriction.locallySurjective_of_restriction,
      ``ManuscriptAudit.EtaleSurjectiveRestriction.epi_of_restriction_epi] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
