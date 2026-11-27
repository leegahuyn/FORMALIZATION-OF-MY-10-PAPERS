import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CoinducedFunctionRestriction
import PrimalitySheafVerification.ManuscriptAudit.CoinducedFunctionQuotient
import PrimalitySheafVerification.ManuscriptAudit.GroupQuotientInvariantSequence

/-!
# Positive group cohomology and normal subgroups

If a representation and its quotient invariants have zero positive
cohomology for the normal subgroup and quotient respectively, the
representation has zero positive cohomology for the whole group.
The proof uses ordinary dimension shifting and the actual coinduced
function representation.
-/

namespace ManuscriptAudit.GroupCohomologyNormalSubgroupAcyclic

open CategoryTheory CategoryTheory.Limits
open CoinducedFunctionRepresentation

universe u

noncomputable section

variable {k G : Type u} [CommRing k] [Group G]

/-- The cokernel sequence of the equivariant embedding in the function
representation. -/
def orbitSequence (A : Rep.{u} k G) : ShortComplex (Rep.{u} k G) :=
  ShortComplex.cokernelSequence (embedding A)

theorem orbitSequence_shortExact (A : Rep.{u} k G) : (orbitSequence A).ShortExact where
  exact := ShortComplex.cokernelSequence_exact (embedding A)
  mono_f := (Rep.mono_iff_injective (embedding A)).mpr (embedding_injective A)
  epi_g := inferInstanceAs (Epi (cokernel.π (embedding A)))

variable (S : Subgroup G) [S.Normal]

set_option backward.isDefEq.respectTransparency false in
/-- Vanishing of all positive subgroup and quotient cohomology implies
vanishing of all positive cohomology for the whole group. -/
theorem H_succ_isZero (n : ℕ) (A : Rep.{u} k G)
    (hSubgroup : ∀ i : ℕ, IsZero (groupCohomology (Rep.res S.subtype A) (i + 1)))
    (hQuotient : ∀ i : ℕ, IsZero (groupCohomology (A.quotientToInvariants S) (i + 1))) :
    IsZero (groupCohomology A (n + 1)) := by
  induction n generalizing A with
  | zero =>
    exact (groupCohomology.H1InfRes_exact A S).isZero_of_both_isZero
      (hQuotient 0) (hSubgroup 0)
  | succ n ih =>
    let X := orbitSequence A
    have hX : X.ShortExact := orbitSequence_shortExact A
    let W := X.map (Rep.resFunctor S.subtype)
    have hW : W.ShortExact := (Rep.shortExact_res S.subtype).mpr hX
    have hZ := GroupQuotientInvariantSequence.shortExact_quotientToInvariants S hX
      (hSubgroup 0)
    have hNewSubgroup (i : ℕ) :
        IsZero (groupCohomology (Rep.res S.subtype X.X₃) (i + 1)) :=
      (groupCohomology.mapShortComplex₃_exact hW (i := i + 1) (j := (i + 1) + 1)
        rfl).isZero_of_both_isZero
        (restrictionFunctions_H_succ_isZero k G A.V S i) (hSubgroup (i + 1))
    have hNewQuotient (i : ℕ) :
        IsZero (groupCohomology (X.X₃.quotientToInvariants S) (i + 1)) :=
      (groupCohomology.mapShortComplex₃_exact hZ (i := i + 1) (j := (i + 1) + 1)
        rfl).isZero_of_both_isZero
        (quotientInvariantsFunctions_H_succ_isZero k G A.V S i) (hQuotient (i + 1))
    letI := groupCohomology.isIso_δ_of_isZero hX (n + 1)
      (functions_H_succ_isZero k G A.V n) (functions_H_succ_isZero k G A.V (n + 1))
    let e := asIso (groupCohomology.δ hX (n + 1) ((n + 1) + 1) rfl)
    exact (ih X.X₃ hNewSubgroup hNewQuotient).of_iso e.symm

end

end ManuscriptAudit.GroupCohomologyNormalSubgroupAcyclic

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.GroupCohomologyNormalSubgroupAcyclic.orbitSequence_shortExact,
      ``ManuscriptAudit.GroupCohomologyNormalSubgroupAcyclic.H_succ_isZero] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
