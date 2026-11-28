import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.PullbackCarrier
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleStageOpenRefinement

/-! An actual affine étale cover at a limiting chart becomes
surjective over one genuine affine étale refinement of its model. -/

namespace ManuscriptAudit.AffineEtaleStageCoverDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ProetaleAffineTensor (structureMap specMap)
open AffineEtaleStageColimit (FiniteTupleApproximation)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A B C E : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing E]
  [Algebra A B] [Algebra A C] [Algebra C E] [Algebra.Etale A C] [Algebra.Etale C E]

set_option maxHeartbeats 2800000 in
/-- If an actual affine étale family (expressed by its affine
disjoint union) covers the limiting chart after base change, it
covers some genuine affine étale refinement after base change. -/
theorem exists_surjective_refinement (hApprox : FiniteTupleApproximation A B)
    (k : C →ₐ[A] B)
    (hCover : Function.Surjective
      (pullback.fst (specMap A k) (structureMap C E))) :
    ∃ (Q : Type u) (_ : CommRing Q) (_ : Algebra A Q), Algebra.Etale A Q ∧
      ∃ (q : C →ₐ[A] Q) (l : Q →ₐ[A] B), l.comp q = k ∧
        Function.Surjective (pullback.fst (specMap A q) (structureMap C E)) := by
  classical
  let f := structureMap C E
  letI : Etale f := (HasRingHomProperty.Spec_iff (P := @Etale) (φ := CommRingCat.ofHom (algebraMap C E))).mpr
    ((RingHom.etale_algebraMap).mpr inferInstance)
  let Z : Set (PrimeSpectrum C) := (Set.range f)ᶜ
  have hZ : IsClosed Z := by
    change IsClosed ((Set.range f)ᶜ)
    exact (f.isOpenMap.isOpen_range).isClosed_compl
  obtain ⟨J, hJ⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal Z).mp hZ
  have hRange (b : PrimeSpectrum B) : specMap A k b ∈ Set.range f := by
    have hb : b ∈ Set.range (pullback.fst (specMap A k) f) := hCover b
    rw [Scheme.Pullback.range_fst] at hb
    exact hb
  have hTop : J.map k.toRingHom = ⊤ := by
    by_contra h
    obtain ⟨p, hMax, hp⟩ := Ideal.exists_le_maximal _ h
    let b : PrimeSpectrum B := ⟨p, hMax.isPrime⟩
    have hb : specMap A k b ∈ PrimeSpectrum.zeroLocus (J : Set C) := by
      intro x hx
      exact hp (Ideal.mem_map_of_mem k.toRingHom hx)
    rw [← hJ] at hb
    exact hb (hRange b)
  obtain ⟨Q, hQR, hQA, hQE, q, l, hlq, hQJ⟩ :=
    AffineEtaleStageOpenRefinement.exists_refinement hApprox k J hTop
  letI : CommRing Q := hQR
  letI : Algebra A Q := hQA
  refine ⟨Q, hQR, hQA, hQE, q, l, hlq, ?_⟩
  intro x
  change x ∈ Set.range (pullback.fst (specMap A q) f)
  rw [Scheme.Pullback.range_fst]
  show specMap A q x ∈ Set.range f
  by_contra hx
  have hz : specMap A q x ∈ PrimeSpectrum.zeroLocus (J : Set C) := hJ ▸ hx
  have hLe : J.map q.toRingHom ≤ x.asIdeal := Ideal.map_le_iff_le_comap.mpr hz
  rw [hQJ] at hLe
  exact x.isPrime.ne_top (top_le_iff.mp hLe)

end
end ManuscriptAudit.AffineEtaleStageCoverDescent

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineEtaleStageCoverDescent.exists_surjective_refinement
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
