import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.FieldEtaleGaloisLocalLifts
import PrimalitySheafVerification.ManuscriptAudit.GaloisCokernelDescent
import PrimalitySheafVerification.ManuscriptAudit.GeometricSkyscraperHigherCohomology
import PrimalitySheafVerification.ManuscriptAudit.SheafH1Descent

/-!
# Degree-one étale cohomology detected on finite Galois covers

A cokernel section representing a degree-one class lifts over some
finite Galois cover. Vanishing of the first group cohomology of the
coefficient sections corrects this lift to a global section.
-/

namespace ManuscriptAudit.FieldEtaleHOneDetection

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FieldEtaleGaloisCovers GaloisCoverAction

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

noncomputable section

variable (K : Type) [Field K]

/-- The first native small-étale cohomology of any additive sheaf on a
field vanishes if degree-one group cohomology vanishes on every finite
Galois extension with the actual section representation. -/
theorem HOne_subsingleton_of_finiteGalois
    (A : Sheaf (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{0})
    (hA : ∀ (L : Type) [Field L] [Algebra K L] [Module.Finite K L] [IsGalois K L],
      Subsingleton (groupCohomology (sectionsRep K L A) 1)) :
    Subsingleton (Sheaf.H A 1) := by
  let I := Injective.under A
  let i : A ⟶ I := Injective.ι A
  let hT : IsTerminal (terminalObject K) := terminalObject_isTerminal K
  apply SheafH1Descent.H1_subsingleton_of_global_lifts i hT
  intro x
  obtain ⟨L, hF, hAlg, hFin, hGal, y, hy⟩ :=
    exists_cokernel_lift_on_finiteGalois_cover K i x
  letI := hF
  letI := hAlg
  letI := hFin
  letI := hGal
  exact exists_global_cokernel_lift_of_HOne K L i (hA L) x y hy

end

end ManuscriptAudit.FieldEtaleHOneDetection

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.FieldEtaleHOneDetection.HOne_subsingleton_of_finiteGalois
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
