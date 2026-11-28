import Lean.Util.CollectAxioms
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import PrimalitySheafVerification.ManuscriptAudit.SpectrumFiniteIdempotentPartition

/-! Every continuous finite-coefficient section on the spectrum of an
exhaustive increasing union is pulled back from a genuine finite stage. -/

namespace ManuscriptAudit.SpectrumFiniteContinuousFactorization

open PrimeSpectrum SpectrumFiniteIdempotentPartition

noncomputable section

variable {K R A : Type*} [CommRing K] [CommRing R] [Algebra K R]
  [Fintype A] [TopologicalSpace A] [DiscreteTopology A]

/-- All fibers descend together to a single actual spectrum of the subalgebra tower. -/
theorem factor (U : ℕ → Subalgebra K R) (hMono : Monotone U)
    (hCover : ∀ r : R, ∃ n, r ∈ U n) (f : PrimeSpectrum R → A) (hf : Continuous f) :
    ∃ (n : ℕ) (g : PrimeSpectrum (U n) → A), Continuous g ∧
      ∀ x, g (PrimeSpectrum.comap (U n).val.toRingHom x) = f x := by
  classical
  obtain ⟨e, he, hfiber⟩ := exists_idempotent_fibers f hf
  choose n hn using fun a => hCover (e a)
  let N := Finset.univ.sup n
  let e' (a : A) : U N :=
    ⟨e a, hMono (Finset.le_sup (f := n) (Finset.mem_univ a)) (hn a)⟩
  have hEq : (U N).val.toRingHom ∘ e' = e := rfl
  have he' : CompleteOrthogonalIdempotents e' :=
    (CompleteOrthogonalIdempotents.map_injective_iff (U N).val.toRingHom
      (fun _ _ h => Subtype.ext h)).mp (hEq.symm ▸ he)
  refine ⟨N, label e' he', label_continuous e' he', fun x => ?_⟩
  apply label_eq_of_mem e' he'
  change x ∈ (basicOpen (e (f x)) : Set (PrimeSpectrum R))
  rw [← hfiber (f x)]
  exact Set.mem_singleton _

end
end ManuscriptAudit.SpectrumFiniteContinuousFactorization

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.SpectrumFiniteContinuousFactorization.factor
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
