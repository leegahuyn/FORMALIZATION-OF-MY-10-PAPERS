import Lean.Util.CollectAxioms
import Mathlib.RingTheory.FinitePresentation
import PrimalitySheafVerification.ManuscriptAudit.CuspNormalizationRecovery
import PrimalitySheafVerification.ManuscriptAudit.EtaleOfSurjectiveSpecBaseChange

/-!
# The conductor-patched cusp algebra is finite étale

Its underlying cusp module is finite projective. The normalization is
surjective on prime spectra and the actual normalization scalar
extension recovers the original étale algebra. This descends
unramifiedness and gives finite étaleness of the patched algebra.
-/

namespace ManuscriptAudit.CuspPatchedFiniteEtale

open AlgebraicGeometry Polynomial
open CuspPunctured CuspEtaleConductorPatch CuspPatchedFiniteProjective CuspNormalizationRecovery
open scoped TensorProduct

noncomputable section

universe u

variable (K : Type u) [Field K]
variable (E : Type u) [CommRing E] [Algebra (Polynomial K) E]
variable [Algebra.Etale (Polynomial K) E] [Module.Finite (Polynomial K) E]

private abbrev A := CuspSubalgebra K
private abbrev L := patchRing K E

local instance descendedAlgebra : Algebra (A K) (L K E) := patchAlgebra K E

private theorem isNoetherianCusp : IsNoetherianRing (A K) := by
  letI : Algebra.FiniteType K (A K) := by
    change Algebra.FiniteType K (Algebra.adjoin K
      ({((X : Polynomial K) ^ 2), (X : Polynomial K) ^ 3} : Set (Polynomial K)))
    exact Algebra.FiniteType.adjoin_of_finite ((Set.finite_singleton _).insert _)
  exact Algebra.FiniteType.isNoetherianRing K (A K)

private theorem normalization_spec_surjective :
    Function.Surjective (PrimeSpectrum.comap (algebraMap (A K) (Polynomial K))) := by
  change Function.Surjective (CuspScheme.cuspMap K)
  exact (surjective_iff (CuspScheme.cuspMap K)).mp (CuspScheme.paper2_cusp_map_surjective K)

/-- An actual finite étale algebra over the polynomial normalization descends
by the conductor construction in every characteristic. -/
theorem conductor_finite_etale :
    Module.Finite (A K) (L K E) ∧ Algebra.Etale (A K) (L K E) := by
  obtain ⟨hFinite, hProjective⟩ := patch_finite_projective K E
  letI := hFinite
  letI := hProjective
  letI : Module.Flat (A K) (L K E) := inferInstance
  letI : IsNoetherianRing (A K) := isNoetherianCusp K
  letI : Algebra.FinitePresentation (A K) (L K E) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  letI : Algebra.Etale (Polynomial K) (Polynomial K ⊗[A K] L K E) :=
    Algebra.Etale.of_equiv (normalizationRecovery K E).symm
  exact ⟨hFinite, EtaleOfSurjectiveSpecBaseChange.etale_of_tensor_etale
    (A K) (Polynomial K) (L K E) (normalization_spec_surjective K)⟩

end

end ManuscriptAudit.CuspPatchedFiniteEtale

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CuspPatchedFiniteEtale.conductor_finite_etale
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
