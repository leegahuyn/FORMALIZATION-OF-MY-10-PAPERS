import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspProperNormalizationProetaleEpi
import PrimalitySheafVerification.ManuscriptAudit.ProetaleExactDirectImagePullback
import PrimalitySheafVerification.ManuscriptAudit.ProetaleDiscreteSchemePullback

/-! The native pullback to the actual proper cusp normalization is
bijective in every degree in positive characteristic. -/

namespace ManuscriptAudit.CuspProperNormalizationNativeCohomology

open AlgebraicGeometry CategoryTheory
open CuspProperCompactification (projectiveCusp)
open CuspProjectiveNormalization (normalizedCusp normalizationMap)
open ProetaleContinuousDirectImageMaps (functions diagonal)
open ProetaleBaseChange (directImage)
open ProetaleSchemeCohomologyPullback (continuous constant)
open ProetaleCohomologyIso (cohomologyIso)
open ProetaleDiscreteSchemePullback (cohomology_pullback)
open ProetaleDiscreteConstant (constantIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] (p : ℕ) [hp : Fact p.Prime] [hchar : CharP K p]

include p hp hchar

private abbrev A := AddCommGrpCat.{1}
private abbrev f := normalizationMap K

set_option maxHeartbeats 6400000 in
/-- Pullback to normalization is bijective for the actual continuous coefficient groups. -/
theorem continuous_bijective (M : Type) [AddCommGroup M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] (n : ℕ) :
    Function.Bijective (continuous (f K) M n) := by
  letI : (directImage (f K) A).PreservesEpimorphisms :=
    { preserves α := CuspProperNormalizationProetaleEpi.map_epi K p α }
  letI : IsFinite (f K) := CuspProperNormalizationHomeomorphism.finite K
  letI : UniversallyInjective (f K) := CuspProperNormalizationHomeomorphism.universallyInjective K
  letI : Surjective (f K) := CuspProperNormalizationHomeomorphism.surjective K
  letI : IsIso (diagonal M (f K)) :=
    ProetaleUniversalHomeomorphismHOne.diagonal_isIso (f K) M
  exact ProetaleExactDirectImagePullback.pullback_bijective (f K) (diagonal M (f K)) n

/-- The proper normalization's actual integral adic pullback is an equivalence. -/
def adicEquiv (l : ℕ) [Fact l.Prime] (n : ℕ) :
    (projectiveCusp K).EllAdicCohomology l n ≃+ (normalizedCusp K).EllAdicCohomology l n :=
  AddEquiv.ofBijective (continuous (f K) ℤ_[l] n) (continuous_bijective K p ℤ_[l] n)

set_option maxHeartbeats 6800000 in
/-- The same actual normalization pullback is bijective for ordinary discrete constant coefficients. -/
theorem constant_bijective (M : Type) [AddCommGroup M] [TopologicalSpace M]
    [DiscreteTopology M] [IsTopologicalAddGroup M] (n : ℕ) :
    Function.Bijective (constant (f K) (AddCommGrpCat.of (ULift.{1} M)) n) := by
  let E := cohomologyIso (constantIso (projectiveCusp K) M) n
  let F := cohomologyIso (constantIso (normalizedCusp K) M) n
  let P := AddEquiv.ofBijective (continuous (f K) M n) (continuous_bijective K p M n)
  let R := E.trans (P.trans F.symm)
  have h : ⇑(constant (f K) (AddCommGrpCat.of (ULift.{1} M)) n) = ⇑R := by
    funext x
    apply F.injective
    change F (constant (f K) (AddCommGrpCat.of (ULift.{1} M)) n x) =
      F (F.symm (P (E x)))
    rw [AddEquiv.apply_symm_apply]
    exact (cohomology_pullback M (f K) n x).symm
  rw [h]
  exact R.bijective

end
end ManuscriptAudit.CuspProperNormalizationNativeCohomology

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``ManuscriptAudit.CuspProperNormalizationNativeCohomology.continuous_bijective,
      ``ManuscriptAudit.CuspProperNormalizationNativeCohomology.adicEquiv,
      ``ManuscriptAudit.CuspProperNormalizationNativeCohomology.constant_bijective] do
    let ax ← collectAxioms n
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{n} depends on unexpected axioms {ax}"
    logInfo m!"{n} uses {ax}"
