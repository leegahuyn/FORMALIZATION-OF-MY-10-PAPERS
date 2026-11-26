import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspCompactSupportSequence
import PrimalitySheafVerification.ManuscriptAudit.CuspProperBoundary
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleExtensionHZero

/-!
# Vanishing in degree zero for the actual compactly supported groups

The affine and punctured cusps have the same boundary point in their
preconnected proper compactification. It forces their degree-zero
compactly supported cohomology to vanish.
-/

namespace ManuscriptAudit.CuspCompactSupportSequence

open AlgebraicGeometry CategoryTheory
open CuspProperCompactification CuspProperBoundary SmallEtaleGeometricBaseChange
open OpenEtaleExtension GeometricSkyscraperCohomology

universe u

noncomputable section

attribute [local instance] etaleSiteHasExt

variable (K : Type u) [Field K] [IsSepClosed K]

/-- Both actual degree-zero compactly supported groups vanish. -/
theorem compactSupportHZero_subsingleton (M : AddCommGrpCat.{u}) :
    Subsingleton (punctureHc K M 0) ∧ Subsingleton (cuspHc K M 0) := by
  letI : PreconnectedSpace (projectiveCusp K) := projectiveCusp_preconnected K
  letI : IsOpenImmersion (affineOpen K) := affineOpen_isOpenImmersion K
  obtain ⟨x, hx⟩ := boundary_geometricPoint K
  let s := geometricPoint K x
  have hp : ¬ ∃ t, t ≫ ((cuspPuncturedOpen K).ι ≫ affineOpen K) = s := by
    rintro ⟨t, ht⟩
    exact hx ⟨t ≫ (cuspPuncturedOpen K).ι, by simpa only [Category.assoc] using ht⟩
  exact ⟨extensionByZeroConstantHZero_subsingleton
      ((cuspPuncturedOpen K).ι ≫ affineOpen K) M s hp,
    extensionByZeroConstantHZero_subsingleton (affineOpen K) M s hx⟩

end

end ManuscriptAudit.CuspCompactSupportSequence

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CuspCompactSupportSequence.compactSupportHZero_subsingleton
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
