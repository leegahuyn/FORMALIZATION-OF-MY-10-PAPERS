import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! A finite product stage's prime localization selects the
corresponding component and its actual prime localization. -/

namespace ManuscriptAudit.FiniteProductStageStalk

noncomputable section

universe u

variable (A : Type u) [CommRing A] {ι : Type u} [Finite ι]
  (D : ι → Type u) [∀ i, CommRing (D i)] [∀ i, Algebra A (D i)]

/-- The algebraic identification of the actual stage stalk respects
the map from the base ring. -/
theorem exists_component (q : PrimeSpectrum (∀ i, D i)) :
    ∃ (i : ι) (p : PrimeSpectrum (D i)),
      q = PrimeSpectrum.comap (Pi.evalRingHom D i) p ∧
      Nonempty (Localization.AtPrime q.asIdeal ≃ₐ[A] Localization.AtPrime p.asIdeal) := by
  obtain ⟨⟨i, p⟩, hp⟩ := (PrimeSpectrum.sigmaToPiHomeo D).surjective q
  rw [PrimeSpectrum.sigmaToPiHomeo_apply, PrimeSpectrum.sigmaToPi_apply] at hp
  refine ⟨i, p, hp.symm, ?_⟩
  subst q
  let f := Localization.AtPrime.mapPiEvalRingHom p.asIdeal
  let e := RingEquiv.ofBijective f (Localization.AtPrime.mapPiEvalRingHom_bijective p.asIdeal)
  refine ⟨AlgEquiv.ofRingEquiv (f := e) (fun a ↦ ?_)⟩
  change f (algebraMap A (Localization.AtPrime
    (p.asIdeal.comap (Pi.evalRingHom D i))) a) = algebraMap A (Localization.AtPrime p.asIdeal) a
  rw [IsScalarTower.algebraMap_apply A (∀ i, D i)
    (Localization.AtPrime (p.asIdeal.comap (Pi.evalRingHom D i)))]
  rw [Localization.AtPrime.mapPiEvalRingHom_algebraMap_apply]
  exact (IsScalarTower.algebraMap_apply A (D i) (Localization.AtPrime p.asIdeal) a).symm

end
end ManuscriptAudit.FiniteProductStageStalk

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.FiniteProductStageStalk.exists_component
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
