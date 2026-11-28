import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Smooth.NoetherianDescent
import Mathlib.RingTheory.TensorProduct.Maps
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleStageFinitePresentationLift

/-! An actual affine étale algebra over the chart has an actual
étale model over one of its affine étale stages. -/

namespace ManuscriptAudit.AffineEtaleStageRelativeDescent

open AlgebraicGeometry CategoryTheory
open ProetaleAffineTensor (structureMap)
open AffineEtaleStageColimit (FiniteTupleApproximation)
open scoped TensorProduct

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A B D : Type u} [CommRing A] [CommRing B] [CommRing D]
  [Algebra A B] [Algebra B D] [IsNoetherianRing A] [WeaklyEtale (structureMap A B)]

set_option maxHeartbeats 3100000 in
/-- An arbitrary affine étale object over the actual chart comes
from an étale object over one actual affine stage of the chart. -/
theorem exists_model [Algebra.Etale B D] (hApprox : FiniteTupleApproximation A B) :
    ∃ (Q : Type u) (_ : CommRing Q) (_ : Algebra A Q), Algebra.Etale A Q ∧
      ∃ (q : Q →ₐ[A] B) (E : Type u) (_ : CommRing E) (_ : Algebra Q E),
        Algebra.Etale Q E ∧
          letI : Algebra Q B := q.toRingHom.toAlgebra
          Nonempty (D ≃ₐ[B] B ⊗[Q] E) := by
  obtain ⟨R, F, hRF, hAF, hR, hEt, ⟨e⟩⟩ :=
    Algebra.Etale.exists_subalgebra_fg A B D
  letI : CommRing F := hRF
  letI : Algebra R F := hAF
  letI : Algebra.Etale R F := hEt
  letI : Algebra.FiniteType A R := (Subalgebra.fg_iff_finiteType R).mp hR
  letI : Algebra.FinitePresentation A R :=
    (Algebra.FinitePresentation.of_finiteType (R := A) (A := R)).mp inferInstance
  obtain ⟨Q, hQ, hAQ, hEtQ, a, q, hqa⟩ :=
    AffineEtaleStageFinitePresentationLift.exists_factorization hApprox R.val
  letI : CommRing Q := hQ
  letI : Algebra A Q := hAQ
  letI : Algebra R Q := a.toRingHom.toAlgebra
  letI : Algebra Q B := q.toRingHom.toAlgebra
  letI : IsScalarTower R Q B := IsScalarTower.of_algebraMap_eq fun r ↦
    (DFunLike.congr_fun hqa r).symm
  let E := Q ⊗[R] F
  letI : Algebra.Etale Q E := inferInstance
  let j : B ⊗[Q] E ≃ₐ[B] B ⊗[R] F :=
    Algebra.TensorProduct.cancelBaseChange R Q B B F
  exact ⟨Q, hQ, hAQ, hEtQ, q, E, inferInstance, inferInstance, inferInstance,
    ⟨e.trans j.symm⟩⟩

end
end ManuscriptAudit.AffineEtaleStageRelativeDescent

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineEtaleStageRelativeDescent.exists_model
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
