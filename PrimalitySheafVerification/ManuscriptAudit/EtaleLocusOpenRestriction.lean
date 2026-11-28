import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Etale.Locus
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAffineTensor

/-! An actual open subscheme of a finitely presented affine scheme
is étale over the base when all its points lie in the étale locus. -/

namespace ManuscriptAudit.EtaleLocusOpenRestriction

open AlgebraicGeometry CategoryTheory
open ProetaleAffineTensor (structureMap)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (A D : Type u) [CommRing A] [CommRing D] [Algebra A D] [Algebra.FinitePresentation A D]

set_option maxHeartbeats 2200000 in
/-- The open's literal structural morphism is étale. -/
theorem etale (U : (ProetaleAffineTensor.spectrum D).Opens)
    (hU : (U : Set (ProetaleAffineTensor.spectrum D)) ⊆ Algebra.etaleLocus A D) :
    Etale (U.ι ≫ structureMap A D) := by
  classical
  let f := U.ι ≫ structureMap A D
  have hh (x : U.toScheme) :
      ∃ (V : Scheme.{u}) (j : V ⟶ U.toScheme),
        IsOpenImmersion j ∧ x ∈ Set.range j ∧ Etale (j ≫ f) := by
    obtain ⟨_, ⟨_, ⟨a, rfl⟩, rfl⟩, hx, ha⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open x.property U.isOpen
    let L := Localization.Away a
    let i : ProetaleAffineTensor.spectrum L ⟶ ProetaleAffineTensor.spectrum D :=
      Spec.map (CommRingCat.ofHom (algebraMap D L))
    letI : IsOpenImmersion i := IsOpenImmersion.of_isLocalization a
    have hi : Set.range i = (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum D)) :=
      PrimeSpectrum.localization_away_comap_range L a
    have hRange : Set.range i ⊆ Set.range U.ι := by
      rw [hi]
      intro p hp
      exact ⟨⟨p, ha hp⟩, rfl⟩
    let j : ProetaleAffineTensor.spectrum L ⟶ U.toScheme := IsOpenImmersion.lift U.ι i hRange
    have hj : j ≫ U.ι = i := IsOpenImmersion.lift_fac U.ι i hRange
    letI : IsOpenImmersion (j ≫ U.ι) := hj.symm ▸ inferInstanceAs (IsOpenImmersion i)
    refine ⟨ProetaleAffineTensor.spectrum L, j, IsOpenImmersion.of_comp j U.ι, ?_, ?_⟩
    · have hx' : x.val ∈ Set.range i := hi.symm ▸ hx
      obtain ⟨z, hz⟩ := hx'
      have he := congrArg (fun g : ProetaleAffineTensor.spectrum L ⟶ ProetaleAffineTensor.spectrum D ↦ g z) hj
      change (j z).val = i z at he
      exact ⟨z, Subtype.ext (he.trans hz)⟩
    · have hEt : Algebra.Etale A L :=
        Algebra.basicOpen_subset_etaleLocus_iff_etale.mp (ha.trans hU)
      have he : i ≫ structureMap A D = structureMap A L :=
        ProetaleAffineTensor.specMap_structureMap A (IsScalarTower.toAlgHom A D L)
      change Etale (j ≫ U.ι ≫ structureMap A D)
      rw [← Category.assoc, hj, he]
      exact (Etale.SpecMap_iff (f := CommRingCat.ofHom (algebraMap A L))).mpr
        ((RingHom.etale_algebraMap).mpr hEt)
  choose V j hJ hCov hEt using hh
  let O : U.toScheme.OpenCover :=
    ⟨⟨U.toScheme, V, j⟩,
      ⟨by simpa using show ∀ x : U.toScheme, ∃ i, ∃ y : V i, j i y = x from
          fun x ↦ ⟨x, hCov x⟩,
        by simpa using hJ⟩⟩
  exact IsZariskiLocalAtSource.of_openCover (P := @Etale) O hEt

end
end ManuscriptAudit.EtaleLocusOpenRestriction

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.EtaleLocusOpenRestriction.etale
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
