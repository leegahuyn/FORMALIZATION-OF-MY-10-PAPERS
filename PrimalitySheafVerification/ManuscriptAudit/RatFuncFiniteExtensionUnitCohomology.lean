import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.RatFuncCyclicUnitCohomology
import PrimalitySheafVerification.ManuscriptAudit.RatFuncTsenFiniteExtension

/-!
# Cyclic cohomology over finite extensions of K(t)

The C1 property of every finite extension gives the norm surjectivity
needed for cyclic even cohomology at each intermediate field.
-/

namespace ManuscriptAudit.RatFuncTsen

/-- Norms are surjective from finite extensions of any finite extension
of the rational function field over an algebraically closed field. -/
theorem finiteExtension_norm_surjective (K F E : Type*) [Field K] [IsAlgClosed K] [Field F]
    [Algebra (RatFunc K) F] [FiniteDimensional (RatFunc K) F] [Field E]
    [Algebra F E] [FiniteDimensional F E] :
    Function.Surjective (fun x : E ↦ Algebra.norm F x) :=
  norm_surjective_of_C1 F E (fun P hP hd hm ↦ exists_finiteExtension_zero K F P hP hd hm)

/-- Positive even cohomology of the actual unit representation vanishes
for a finite cyclic Galois extension of any finite extension of K(t). -/
theorem finiteExtension_cyclic_units_even_subsingleton (K F E : Type) [Field K] [IsAlgClosed K]
    [Field F] [Algebra (RatFunc K) F] [FiniteDimensional (RatFunc K) F] [Field E]
    [Algebra F E] [FiniteDimensional F E] [IsGalois F E] [IsCyclic (E ≃ₐ[F] E)]
    (g : E ≃ₐ[F] E) (hg : ∀ x, x ∈ Subgroup.zpowers g) (i : ℕ) [NeZero i] (hi : Even i) :
    Subsingleton (groupCohomology (Rep.ofAlgebraAutOnUnits F E) i) :=
  cyclic_units_even_subsingleton_of_norm F E (finiteExtension_norm_surjective K F E) g hg i hi

end ManuscriptAudit.RatFuncTsen

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.RatFuncTsen.finiteExtension_norm_surjective,
      ``ManuscriptAudit.RatFuncTsen.finiteExtension_cyclic_units_even_subsingleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
