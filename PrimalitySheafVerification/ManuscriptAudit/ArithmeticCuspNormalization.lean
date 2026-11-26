import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspNormalizationConstants
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleClosedResidue

/-!
# Arithmetic cusp normalization and its claimed delta summand

At the rational origin of the cusp over F₅, the normalization
quotient has delta one. The actual coefficient cokernel of
normalization is zero. The closed arithmetic residue pushforward
for Z/2 coefficients is nonzero and cannot be its direct summand.
-/

namespace ManuscriptAudit.ArithmeticCuspNormalization

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

private abbrev K := ZMod 5
private abbrev R := CuspPunctured.CuspSubalgebra K
private abbrev coefficient := AddCommGrpCat.of (ZMod 2)
private abbrev site := (Spec (CommRingCat.of R)).smallEtaleTopology

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The delta quotient for the specific arithmetic cusp has dimension one. -/
theorem cusp_delta_one :
    Module.finrank K (Polynomial K ⧸ R.toSubmodule) = 1 :=
  CuspDelta.paper2_cusp_delta_coordinate_quotient_finrank K

/-- The actual cokernel of the constant-to-normalization coefficient map. -/
def coefficientCokernel : Sheaf site AddCommGrpCat.{0} :=
  cokernel (CuspNormalizationConstants.normalizationMap K 5 coefficient)

/-- The origin term using the arithmetic residue field in the small étale site. -/
def arithmeticOriginTerm : Sheaf site AddCommGrpCat.{0} :=
  (SmallEtaleBaseChange.directImage SmallEtaleClosedResidue.cuspOrigin AddCommGrpCat.{0}).obj
    ((constantSheaf (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{0}).obj coefficient)

/-- The printed order-one delta summand cannot occur in the normalization
cokernel, even as a summand of an isomorphic sheaf. -/
theorem paper2_arithmetic_delta_summand_refuted
    (Q : Sheaf site AddCommGrpCat.{0}) (e : coefficientCokernel ≅ Q)
    (inclusion : arithmeticOriginTerm ⟶ Q) (projection : Q ⟶ arithmeticOriginTerm)
    (split : inclusion ≫ projection = 𝟙 arithmeticOriginTerm) : False := by
  have hZero : IsZero Q :=
    (CuspNormalizationConstants.normalizationCokernel_isZero K 5 coefficient).of_iso e.symm
  have hProjection : projection = 0 := hZero.eq_of_src _ _
  have hid : 𝟙 arithmeticOriginTerm = 0 := by
    calc
      𝟙 arithmeticOriginTerm = inclusion ≫ projection := split.symm
      _ = 0 := by rw [hProjection, comp_zero]
  exact SmallEtaleClosedResidue.arithmetic_cusp_origin_cyclic_pushforward_not_isZero
    ((IsZero.iff_id_eq_zero arithmeticOriginTerm).mpr hid)

end

end ManuscriptAudit.ArithmeticCuspNormalization

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.ArithmeticCuspNormalization.cusp_delta_one,
      ``ManuscriptAudit.ArithmeticCuspNormalization.paper2_arithmetic_delta_summand_refuted] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
