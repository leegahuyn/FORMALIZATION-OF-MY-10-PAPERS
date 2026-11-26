import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Sites.LocallySurjective
import PrimalitySheafVerification.ManuscriptAudit.CertifiedTorsorSplit
import PrimalitySheafVerification.ManuscriptAudit.CertifiedTorsorSplitTrace
import PrimalitySheafVerification.ManuscriptAudit.KummerSiteCover
import PrimalitySheafVerification.ManuscriptAudit.NodalSwapCoverSheafTrace

/-!
# Local surjectivity of the actual nodal trace

Over the refinement by the crossed cover, the second projection is
an actual section of the base-changed two-sheet comparison. The
resulting exchanged clopen halves lift every local trace section.
-/

namespace ManuscriptAudit.NodalSwapCoverLocalTrace

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open NodalConductor NodalSwapCover NodalSwapCoverEtale
open AffineEtaleTensorPresentation NodalSwapCoverAffineTrace NodalSwapCoverSheafTrace
open scoped TensorProduct

noncomputable section

universe u

variable (K : Type u) [Field K]

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A : Type u := ↥(coordinates K)
private abbrev E : Type u := Cover K
private abbrev X := base (A K)
private abbrev aff := (X K).AffineEtale
private abbrev site := Scheme.AffineEtale.topology (X K)

attribute [local instance] objectAlgebra

variable (R : Type u) [CommRing R] [Algebra (A K) R]
variable (M : AddCommGrpCat.{u}) [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalAddGroup M]

set_option maxHeartbeats 1600000 in
theorem affineTrace_surjective_of_section (h2 : (2 : K) ≠ 0) (g : E K →ₐ[A K] R) :
    Function.Surjective (affineTrace K R M h2) := by
  letI : Algebra (E K) R := g.toRingHom.toAlgebra
  letI : IsScalarTower (A K) (E K) R := IsScalarTower.of_algHom g
  letI : Module.Finite (A K) (E K) := (cover_finite_etale K h2).1
  letI : Module.FaithfullyFlat (A K) (E K) := cover_faithfullyFlat K h2
  let c := NodalSwapCoverTorsor.certificate K h2
  let e := CertifiedTorsorSplit.firstIdempotent (A K) (E K) R (swap K) c
  let f := CertifiedTorsorSplit.secondIdempotent (A K) (E K) R (swap K) c
  exact CertifiedTorsorSpectrumTrace.spectrumTrace_surjective_of_idempotents R (coverOver K R)
    (coverOverSwap K R)
    (InvolutionTensorBaseChange.baseSwap_involutive (A K) (E K) R (swap K) (swap_twice K))
    (coverOverCertificate K R h2) inferInstance inferInstance e f
    (CertifiedTorsorSplit.idempotents_mul (A K) (E K) R (swap K) c)
    (CertifiedTorsorSplit.idempotents_add (A K) (E K) R (swap K) c)
    (CertifiedTorsorSplit.deck_firstIdempotent (A K) (E K) R (swap K) c (swap_twice K))

variable (U : aff K)

private theorem tensorFirst_etale (h2 : (2 : K) ≠ 0) :
    Etale (tensorFirst (A K) (E K) U) := by
  letI : Algebra.Etale (A K) (E K) := (cover_finite_etale K h2).2
  change Etale (Spec.map
    (CommRingCat.ofHom (algebraMap (objectRing (A K) U) (tensorRing (A K) (E K) U))))
  exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr (inferInstance :
      Algebra.Etale (objectRing (A K) U) (tensorRing (A K) (E K) U)))

def refinement (h2 : (2 : K) ≠ 0) : aff K := by
  letI : Etale U.hom := U.prop
  letI : Etale (tensorFirst (A K) (E K) U) := tensorFirst_etale K U h2
  exact Scheme.AffineEtale.mk (tensorFirst (A K) (E K) U ≫ U.hom)

def refinementArrow (h2 : (2 : K) ≠ 0) : refinement K U h2 ⟶ U :=
  MorphismProperty.CostructuredArrow.homMk
    (CommRingCat.ofHom
      ((Algebra.TensorProduct.includeLeft : objectRing (A K) U →ₐ[A K]
        tensorRing (A K) (E K) U).toRingHom)).op trivial rfl

theorem refinement_cover (h2 : (2 : K) ≠ 0) :
    Sieve.ofArrows (fun _ : Unit => refinement K U h2)
      (fun _ : Unit => refinementArrow K U h2) ∈ site K U := by
  rw [Scheme.AffineEtale.topology, Functor.mem_inducedTopology_iff_of_isCoverDense,
    Sieve.functorPushforward_ofArrows]
  apply KummerSiteCover.singleton_mem_smallEtaleTopology
  letI : Module.FaithfullyFlat (A K) (E K) := cover_faithfullyFlat K h2
  change Function.Surjective (PrimeSpectrum.comap
    (algebraMap (objectRing (A K) U) (tensorRing (A K) (E K) U)))
  exact PrimeSpectrum.comap_surjective_of_faithfullyFlat

set_option maxHeartbeats 1500000 in
def refinementSection (h2 : (2 : K) ≠ 0) :
    E K →ₐ[A K] objectRing (A K) (refinement K U h2) where
  __ := (Algebra.TensorProduct.includeRight :
    E K →ₐ[A K] tensorRing (A K) (E K) U).toRingHom
  commutes' := by
    intro a
    have hcomm :
        CommRingCat.ofHom (algebraMap (A K) (E K)) ≫ CommRingCat.ofHom
          ((Algebra.TensorProduct.includeRight : E K →ₐ[A K] tensorRing (A K) (E K) U).toRingHom) =
          structureRingHom (A K) (refinement K U h2) := by
      apply Spec.map_injective
      rw [Spec.map_comp, spec_structureRingHom]
      exact (tensor_isPullback (A K) (E K) U).w.symm
    exact congrArg (fun p : CommRingCat.of (A K) ⟶ objectRing (A K) (refinement K U h2) =>
      p.hom a) hcomm

set_option maxHeartbeats 1700000 in
theorem trace_isLocallySurjective (h2 : (2 : K) ≠ 0) :
    Sheaf.IsLocallySurjective (trace K M h2) where
  imageSieve_mem {U} s := by
    refine (site K).superset_covering ?_ (refinement_cover K U h2)
    apply (Sieve.generate_le_iff _ _).2
    rintro _ _ ⟨i⟩
    exact trace_app_surjective_of_affine_trace_surjective K M h2 (refinement K U h2)
      (affineTrace_surjective_of_section K (objectRing (A K) (refinement K U h2)) M h2
        (refinementSection K U h2)) ((baseFunctions K M).obj.map (refinementArrow K U h2).op s)

theorem trace_epi (h2 : (2 : K) ≠ 0) : Epi (trace K M h2) := by
  letI : Sheaf.IsLocallySurjective (trace K M h2) := trace_isLocallySurjective K M h2
  infer_instance

end

end ManuscriptAudit.NodalSwapCoverLocalTrace

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in
    [``ManuscriptAudit.NodalSwapCoverLocalTrace.affineTrace_surjective_of_section,
      ``ManuscriptAudit.NodalSwapCoverLocalTrace.refinement_cover,
      ``ManuscriptAudit.NodalSwapCoverLocalTrace.refinementSection,
      ``ManuscriptAudit.NodalSwapCoverLocalTrace.trace_isLocallySurjective,
      ``ManuscriptAudit.NodalSwapCoverLocalTrace.trace_epi] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter (fun axiomName => !allowed.contains axiomName)
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
