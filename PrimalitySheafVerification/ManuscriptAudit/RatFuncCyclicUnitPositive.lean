import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.RatFuncFiniteExtensionUnitCohomology

/-!
# All positive unit cohomology of cyclic extensions over K(t)

The native cyclic resolution identifies each odd group with the first
group, which vanishes by Hilbert 90. Tsen's norm surjectivity gives
vanishing of all positive even groups.
-/

namespace ManuscriptAudit.RatFuncTsen

open CategoryTheory Rep.FiniteCyclicGroup

/-- All positive cohomology of the actual unit representation vanishes
for a finite cyclic Galois extension of any finite extension of K(t). -/
theorem finiteExtension_cyclic_units_H_succ_subsingleton (K F L : Type)
    [Field K] [IsAlgClosed K] [Field F] [Algebra (RatFunc K) F]
    [FiniteDimensional (RatFunc K) F] [Field L] [Algebra F L] [FiniteDimensional F L]
    [IsGalois F L] [IsCyclic (L ≃ₐ[F] L)] (n : ℕ) :
    Subsingleton (groupCohomology (Rep.ofAlgebraAutOnUnits F L) (n + 1)) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := L ≃ₐ[F] L)
  rcases Nat.even_or_odd (n + 1) with he | ho
  · exact finiteExtension_cyclic_units_even_subsingleton K F L g hg (n + 1) he
  · letI : CommGroup (L ≃ₐ[F] L) := IsCyclic.commGroup
    let A := Rep.ofAlgebraAutOnUnits F L
    let e := groupCohomologyIsoOdd A g hg (n + 1) ho ≪≫
      (groupCohomologyIsoOdd A g hg 1 (by decide)).symm
    have hij : Function.Injective e.hom := (ModuleCat.mono_iff_injective _).mp inferInstance
    exact ⟨fun x y ↦ hij (Subsingleton.elim _ _)⟩

end ManuscriptAudit.RatFuncTsen

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.RatFuncTsen.finiteExtension_cyclic_units_H_succ_subsingleton
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
