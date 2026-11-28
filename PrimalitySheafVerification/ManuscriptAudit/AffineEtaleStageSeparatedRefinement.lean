import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleStageCoverDescent
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleStageCoverGeometry

/-! A common affine chart cover witnesses equality at a genuine
surjective étale refinement of an actual base stage. -/

namespace ManuscriptAudit.AffineEtaleStageSeparatedRefinement

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ProetaleAffineTensor (structureMap specMap)
open AffineEtaleStageColimit (FiniteTupleApproximation)
open scoped TensorProduct

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {A B C D N : Type u}
  [CommRing A] [CommRing B] [CommRing C] [CommRing D] [CommRing N]
  [Algebra A B] [Algebra A C] [Algebra A D] [Algebra A N]
  [Algebra.Etale A C] [Algebra.Etale A N]

set_option maxHeartbeats 6500000 in
/-- The two actual stage maps agree above an actual étale cover of
some refinement of the target stage. The cover is surjective because
the original chart cover factors through its base change. -/
theorem exists_cover_refinement
    (hApprox : FiniteTupleApproximation A B)
    (t : C →ₐ[A] B) (p q : C →ₐ[A] N) (r : N →ₐ[A] D) (k : B →ₐ[A] D)
    (hp : r.comp p = k.comp t) (hq : r.comp q = k.comp t)
    (hCov : Function.Surjective (specMap A k)) :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra A T), Algebra.Etale A T ∧
      ∃ (a : C →ₐ[A] T) (b : T →ₐ[A] B), b.comp a = t ∧
        ∃ (V : Type u) (_ : CommRing V) (_ : Algebra A V), Algebra.Etale A V ∧
          ∃ (e : T →ₐ[A] V) (s : N →ₐ[A] V), Function.Surjective (specMap A e) ∧
            s.comp p = e.comp a ∧ s.comp q = e.comp a := by
  obtain ⟨Q, hQR, hQA, hQE, a₀, b₀, hEq, hQ⟩ :=
    AffineEtaleStageCoequalizer.exists_coequalizer p q r (hp.trans hq.symm)
  letI : CommRing Q := hQR
  letI : Algebra A Q := hQA
  letI : Algebra.Etale A Q := hQE
  let c : C →ₐ[A] Q := a₀.comp p
  letI : Algebra C Q := c.toRingHom.toAlgebra
  letI : IsScalarTower A C Q := IsScalarTower.of_algebraMap_eq (fun x ↦ (c.commutes x).symm)
  letI : Algebra.Etale C Q := Algebra.Etale.of_restrictScalars A C Q
  have hC : k.comp t = b₀.comp c := by
    calc
      _ = r.comp p := hp.symm
      _ = (b₀.comp a₀).comp p := congrArg (fun u ↦ u.comp p) hQ.symm
      _ = _ := rfl
  have hSurj : Function.Surjective (pullback.fst (specMap A t) (structureMap C Q)) :=
    AffineEtaleStageCoverGeometry.pullback_surjective_of_factor t c k b₀ hC hCov
  obtain ⟨T, hTR, hTA, hTE, a, b, hT, hPull⟩ :=
    AffineEtaleStageCoverDescent.exists_surjective_refinement hApprox t (E := Q) hSurj
  letI : CommRing T := hTR
  letI : Algebra A T := hTA
  letI : Algebra.Etale A T := hTE
  letI : Algebra C T := a.toRingHom.toAlgebra
  letI : IsScalarTower A C T := IsScalarTower.of_algebraMap_eq (fun x ↦ (a.commutes x).symm)
  let V := T ⊗[C] Q
  letI : Algebra A V := inferInstanceAs (Algebra A (T ⊗[C] Q))
  letI : IsScalarTower A T V := inferInstanceAs (IsScalarTower A T (T ⊗[C] Q))
  letI : IsScalarTower A C V := inferInstanceAs (IsScalarTower A C (T ⊗[C] Q))
  letI : Algebra.Etale A V := Algebra.Etale.comp A T V
  let e : T →ₐ[A] V := IsScalarTower.toAlgHom A T V
  let j : Q →ₐ[C] V := Algebra.TensorProduct.includeRight
  let s : N →ₐ[A] V := (j.restrictScalars A).comp a₀
  have hCover : Function.Surjective (specMap A e) :=
    AffineEtaleStageCoverGeometry.tensor_surjective (R := C) (S := T) (T := Q) hPull
  have hMatch : s.comp p = e.comp a := by
    apply AlgHom.ext
    intro x
    change j (algebraMap C Q x) = algebraMap T V (algebraMap C T x)
    rw [← IsScalarTower.algebraMap_apply C T V]
    exact j.commutes x
  have hMatch' : s.comp q = e.comp a := by
    calc
      _ = (j.restrictScalars A).comp (a₀.comp q) := rfl
      _ = (j.restrictScalars A).comp (a₀.comp p) := congrArg (j.restrictScalars A).comp hEq.symm
      _ = s.comp p := rfl
      _ = _ := hMatch
  exact ⟨T, hTR, hTA, hTE, a, b, hT, V, inferInstance, inferInstance, inferInstance,
    e, s, hCover, hMatch, hMatch'⟩

end
end ManuscriptAudit.AffineEtaleStageSeparatedRefinement

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineEtaleStageSeparatedRefinement.exists_cover_refinement
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
