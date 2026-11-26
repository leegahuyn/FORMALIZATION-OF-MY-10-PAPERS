import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Localization.Away.Basic
import PrimalitySheafVerification.ManuscriptAudit.NodalConductor

/-! The nodal normalization is an isomorphism off the conductor point. -/

namespace ManuscriptAudit.NodalAwayNormalization

open Polynomial NodalConductor

noncomputable section

variable (K : Type*) [Field K]

def nodeX : coordinates K := ⟨x K, Algebra.subset_adjoin (by simp)⟩

def awayMap : Localization.Away (nodeX K) →ₐ[K] Localization.Away (x K) :=
  Localization.awayMapₐ (coordinates K).val (nodeX K)

private theorem awayMap_injective : Function.Injective (awayMap K) := by
  change Function.Injective (Localization.awayMap (coordinates K).val.toRingHom (nodeX K))
  apply Localization.awayMap_injective_iff.mpr
  intro a ha
  have hz : a = 0 := Subtype.ext ha
  exact ⟨0, by rw [hz, mul_zero]⟩

private theorem awayMap_surjective : Function.Surjective (awayMap K) := by
  change Function.Surjective (Localization.awayMap (coordinates K).val.toRingHom (nodeX K))
  apply Localization.awayMap_surjective_iff.mpr
  intro a
  refine ⟨⟨x K * a, x_mul_mem_coordinates K a⟩, 1, ?_⟩
  change x K * a = x K ^ 1 * a
  rw [pow_one]

/-- The open complement of the node is the polynomial line localized at t² − 1. -/
def normalizationEquiv :
    Localization.Away (nodeX K) ≃ₐ[K] Localization.Away (x K) :=
  AlgEquiv.ofBijective (awayMap K) ⟨awayMap_injective K, awayMap_surjective K⟩

end
end ManuscriptAudit.NodalAwayNormalization

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.NodalAwayNormalization.normalizationEquiv
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
