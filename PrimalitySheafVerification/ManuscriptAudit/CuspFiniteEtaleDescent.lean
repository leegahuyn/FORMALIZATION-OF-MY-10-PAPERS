import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspFiniteEtaleCategory
import PrimalitySheafVerification.ManuscriptAudit.CuspPatchedFiniteEtale

/-!
# The native finite étale categories of the cusp and normalization

Every finite étale algebra on the polynomial normalization descends by
the actual conductor ring pullback. Homomorphisms descend by their
native scalar-extension bijection, giving an equivalence.
-/

namespace ManuscriptAudit.CuspFiniteEtaleDescent

open CategoryTheory CommAlgCat
open CuspPunctured CuspEtaleConductorPatch CuspNormalizationRecovery

noncomputable section

universe u

variable (K : Type u) [Field K]

private abbrev A := CuspSubalgebra K
private abbrev B := Polynomial K

/-- The object-descent input is supplied by the actual conductor pullback. -/
theorem hasFiniteEtaleDescent : CuspFiniteEtaleCategory.HasFiniteEtaleDescent K := by
  intro E
  let T := patchRing K E
  letI : Algebra (A K) T := patchAlgebra K E
  obtain ⟨hFinite, hEtale⟩ := CuspPatchedFiniteEtale.conductor_finite_etale K E
  letI := hFinite
  letI := hEtale
  refine ⟨FiniteEtale.of (A K) T, ⟨?_⟩⟩
  exact normalizationRecovery K E

/-- Normalization gives an equivalence of actual finite étale categories
over the cusp in arbitrary characteristic. -/
def equivalence : FiniteEtale.{u} (A K) ≌ FiniteEtale.{u} (B K) :=
  CuspFiniteEtaleCategory.finiteEtaleEquivalence K (hasFiniteEtaleDescent K)

end

end ManuscriptAudit.CuspFiniteEtaleDescent

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CuspFiniteEtaleDescent.hasFiniteEtaleDescent,
      ``ManuscriptAudit.CuspFiniteEtaleDescent.equivalence] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
