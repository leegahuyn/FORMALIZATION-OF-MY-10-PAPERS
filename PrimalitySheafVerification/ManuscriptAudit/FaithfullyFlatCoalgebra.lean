import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import PrimalitySheafVerification.ManuscriptAudit.FaithfullyFlatRankOne

/-!
# Rank-one coalgebras for faithfully flat scalar extension

A coalgebra for the actual extension-restriction comonad with underlying
free (B)-module of rank one is isomorphic to the comparison coalgebra
of the base ring when the base is a PID.
-/

namespace ManuscriptAudit.FaithfullyFlatCoalgebra

open CategoryTheory ModuleCat TensorProduct

universe u

noncomputable section

variable {R B : Type u} [CommRing R] [CommRing B]
variable [IsDomain R] [IsPrincipalIdealRing R]

/-- Comonadicity and PID rank-one descent make the underlying rank-one
coalgebra a scalar extension of the standard module over the base. -/
theorem rank_one_coalgebra_is_standard (f : R →+* B) (hf : f.FaithfullyFlat)
    (D : (extendRestrictScalarsAdj f).toComonad.Coalgebra)
    (eA : D.A ≅ ModuleCat.of B B) :
    Nonempty ((Comonad.comparison (extendRestrictScalarsAdj f)).obj (ModuleCat.of R R) ≅ D) := by
  letI : Algebra R B := f.toAlgebra
  letI : Module.FaithfullyFlat R B := hf
  let C := Comonad.comparison (extendRestrictScalarsAdj f)
  letI : C.IsEquivalence := (comonadicExtendScalars hf).eqv
  let E := C.asEquivalence
  let M := E.inverse.obj D
  let eD : C.obj M ≅ D := E.counitIso.app D
  let eB : (extendScalars f).obj M ≅ ModuleCat.of B B :=
    ((extendRestrictScalarsAdj f).toComonad.forget.mapIso eD) ≪≫ eA
  have eM : (B ⊗[R] M) ≃ₗ[B] B := eB.toLinearEquiv
  obtain ⟨eR⟩ := FaithfullyFlatRankOne.rank_one_descends_over_pid R B M eM
  exact ⟨C.mapIso eR.symm.toModuleIso ≪≫ eD⟩

end

end ManuscriptAudit.FaithfullyFlatCoalgebra

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.FaithfullyFlatCoalgebra.rank_one_coalgebra_is_standard
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
