import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.RatFuncTsenFiniteExtension
import PrimalitySheafVerification.ManuscriptAudit.SplitDivisionAlgebraCOne

/-!
# Split division algebras over finite extensions of K(t)

Tsen's homogeneous equation theorem implies that any finite-dimensional
division algebra admitting a finite Galois splitting has dimension one.
-/

namespace ManuscriptAudit.RatFuncSplitDivisionAlgebra

open scoped TensorProduct

/-- For a finite extension of the rational function field over an
algebraically closed field, every finite-dimensional division algebra
with a finite Galois splitting has dimension one. -/
theorem finrank_eq_one (K F L D : Type*) [Field K] [IsAlgClosed K] [Field F]
    [Algebra (RatFunc K) F] [FiniteDimensional (RatFunc K) F]
    [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    [DivisionRing D] [Algebra F D] [FiniteDimensional F D] {n : ℕ}
    (s : L ⊗[F] D ≃ₐ[L] Matrix (Fin n) (Fin n) L) :
    Module.finrank F D = 1 := by
  letI : Infinite (RatFunc K) :=
    Infinite.of_injective (algebraMap K (RatFunc K)) (RingHom.injective _)
  letI : Infinite F := Infinite.of_injective (algebraMap (RatFunc K) F) (RingHom.injective _)
  letI : Infinite L := Infinite.of_injective (algebraMap F L) (RingHom.injective _)
  apply SplitDivisionAlgebraCOne.finrank_eq_one s
  intro a d P hP hd ha
  exact RatFuncTsen.exists_finiteExtension_zero K F P hP hd ha

end ManuscriptAudit.RatFuncSplitDivisionAlgebra

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.RatFuncSplitDivisionAlgebra.finrank_eq_one
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
