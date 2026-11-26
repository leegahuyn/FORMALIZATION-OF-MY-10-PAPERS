import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NestedOpenRationalOriginQuotient

/-!
# Open–closed sequence for the actual cusp origin

The missing point is the constant-coefficient origin of the cusp
coordinate ring. For an open cusp chart with a rational origin section,
the right-hand term of the sequence is the direct image from that origin.
-/

namespace ManuscriptAudit.SmallEtaleGeometricBaseChange

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits OpenEtaleExtension

noncomputable section

universe u

variable (K : Type u) [Field K] [IsSepClosed K]

private abbrev S := Spec (CommRingCat.of K)
private abbrev U := Spec (CommRingCat.of (CuspPunctured.CuspSubalgebra K))

/-- The punctured cusp is the open complement of the actual rational origin. -/
def cuspPuncturedOpen : (U K).Opens :=
  letI := cuspOrigin_closedImmersion K
  ⟨(Set.range (cuspOrigin K))ᶜ, (cuspOrigin K).isClosedEmbedding.isClosed_range.isOpen_compl⟩

private theorem cuspPuncturedOpen_range :
    Set.range (cuspPuncturedOpen K).ι = (Set.range (cuspOrigin K))ᶜ := by
  change ((cuspPuncturedOpen K).ι.opensRange : Set (U K)) = (Set.range (cuspOrigin K))ᶜ
  rw [Scheme.Opens.opensRange_ι]
  rfl

/-- The genuine open–closed complex for a cusp chart and its puncture. -/
def cuspOpenOriginSequence {X : Scheme.{u}} (j : U K ⟶ X) [IsOpenImmersion j]
    (π : X ⟶ S K) (ho : (cuspOrigin K ≫ j) ≫ π = 𝟙 (S K))
    (M : AddCommGrpCat.{u}) : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
  letI := isClosedImmersion_of_comp_eq_id π (cuspOrigin K ≫ j) ho
  nestedOpenRationalOriginSequence (cuspPuncturedOpen K).ι j M (cuspOrigin K)
    (cuspPuncturedOpen_range K)

theorem cuspOpenOriginSequence_shortExact {X : Scheme.{u}} (j : U K ⟶ X) [IsOpenImmersion j]
    (π : X ⟶ S K) (ho : (cuspOrigin K ≫ j) ≫ π = 𝟙 (S K))
    (M : AddCommGrpCat.{u}) : (cuspOpenOriginSequence K j π ho M).ShortExact :=
  letI := isClosedImmersion_of_comp_eq_id π (cuspOrigin K ≫ j) ho
  nestedOpenRationalOriginSequence_shortExact (cuspPuncturedOpen K).ι j M (cuspOrigin K)
    (cuspPuncturedOpen_range K)

end

end ManuscriptAudit.SmallEtaleGeometricBaseChange

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.SmallEtaleGeometricBaseChange.cuspOpenOriginSequence_shortExact
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
