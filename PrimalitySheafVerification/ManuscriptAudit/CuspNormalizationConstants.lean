import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleBaseChange
import PrimalitySheafVerification.ManuscriptAudit.CuspAffineEtaleEquivalence
import PrimalitySheafVerification.ManuscriptAudit.CuspConductorSquare
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleCohomologyComparison
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleSkyscraper

/-!
# The actual normalization map on constant étale sheaves

In prime characteristic the normalization direct image is an
equivalence on the full small étale sheaf categories. The map
from the constant cusp sheaf is the unit of the pullback/direct
image adjunction, composed with constant-coefficient comparison.
-/

namespace ManuscriptAudit.CuspNormalizationConstants

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CuspAffineEtale AffineEtaleBaseChange

noncomputable section

variable (K : Type) [Field K] (p : ℕ) [pPrime : Fact p.Prime] [kCharP : CharP K p]

private abbrev cuspSite := (Cusp K).smallEtaleTopology
private abbrev normalizationSite := (Normalization K).smallEtaleTopology

private theorem cusp_surjective : Function.Surjective (CuspScheme.cuspMap K) :=
  (surjective_iff (CuspScheme.cuspMap K)).mp (CuspScheme.paper2_cusp_map_surjective K)

include p pPrime kCharP

/-- The full étale sheaf equivalence with normalization direct image as its forward functor. -/
def normalizationDirectImageEquiv :
    Sheaf (normalizationSite K) AddCommGrpCat.{0} ≌ Sheaf (cuspSite K) AddCommGrpCat.{0} := by
  letI := affinePullback_isEquivalence K p
  exact canonicalFullSheafEquivalence (CuspScheme.cuspMap K) (cusp_surjective K)
    (affinePullback K) (affinePullbackSpecIso K)

private def pullbackConstantIso (A : AddCommGrpCat.{0}) :
    (normalizationDirectImageEquiv K p).inverse.obj
        ((constantSheaf (cuspSite K) AddCommGrpCat.{0}).obj A) ≅
      (constantSheaf (normalizationSite K) AddCommGrpCat.{0}).obj A := by
  letI := affinePullback_isEquivalence K p
  exact (canonicalPullbackConstantComparison (CuspScheme.cuspMap K) (cusp_surjective K)
    (affinePullback K) (affinePullbackSpecIso K)).app A

private def normalizationIso (A : AddCommGrpCat.{0}) :
    (constantSheaf (cuspSite K) AddCommGrpCat.{0}).obj A ≅
      (normalizationDirectImageEquiv K p).functor.obj
        ((constantSheaf (normalizationSite K) AddCommGrpCat.{0}).obj A) :=
  let e := normalizationDirectImageEquiv K p
  e.symm.unitIso.app _ ≪≫ e.functor.mapIso (pullbackConstantIso K p A)

/-- The canonical normalization arrow given by adjunction from pullback comparison. -/
def normalizationMap (A : AddCommGrpCat.{0}) :
    (constantSheaf (cuspSite K) AddCommGrpCat.{0}).obj A ⟶
      (normalizationDirectImageEquiv K p).functor.obj
        ((constantSheaf (normalizationSite K) AddCommGrpCat.{0}).obj A) :=
  (normalizationIso K p A).hom

theorem normalizationMap_isIso (A : AddCommGrpCat.{0}) : IsIso (normalizationMap K p A) :=
  (normalizationIso K p A).isIso_hom

/-- The coefficient cokernel in the normalization sequence is the zero sheaf. -/
theorem normalizationCokernel_isZero (A : AddCommGrpCat.{0}) :
    IsZero (cokernel (normalizationMap K p A)) := by
  letI := normalizationMap_isIso K p A
  exact isZero_cokernel_of_epi _

/-- No nonzero sheaf is isomorphic to the actual coefficient cokernel. -/
theorem normalizationCokernel_not_nonzero (A : AddCommGrpCat.{0})
    (Q : Sheaf (cuspSite K) AddCommGrpCat.{0}) (hQ : ¬ IsZero Q) :
    ¬ Nonempty (cokernel (normalizationMap K p A) ≅ Q) := by
  rintro ⟨e⟩
  exact hQ ((normalizationCokernel_isZero K p A).of_iso e.symm)


/-- The positive delta of the cusp cannot contribute a geometric
skyscraper summand to the constant-coefficient normalization cokernel. -/
theorem normalizationCokernel_not_originSkyscraper [IsSepClosed K]
    (A : AddCommGrpCat.{0}) (hA : ¬ IsZero A) :
    ¬ Nonempty (cokernel (normalizationMap K p A) ≅
      (Scheme.pointSmallEtale (Spec.map (CuspConductorSquare.origin K))).skyscraperSheaf A) :=
  normalizationCokernel_not_nonzero K p A _
    (SmallEtaleSkyscraper.skyscraper_not_isZero _ A hA)

end

end ManuscriptAudit.CuspNormalizationConstants

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CuspNormalizationConstants.normalizationMap_isIso,
      ``ManuscriptAudit.CuspNormalizationConstants.normalizationCokernel_isZero,
      ``ManuscriptAudit.CuspNormalizationConstants.normalizationCokernel_not_nonzero,
      ``ManuscriptAudit.CuspNormalizationConstants.normalizationCokernel_not_originSkyscraper] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
