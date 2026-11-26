import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Localization.Away.Basic
import PrimalitySheafVerification.ManuscriptAudit.NodalConductor

/-! The nodal normalization is an isomorphism off the conductor point. -/

namespace ManuscriptAudit.NodalAwayNormalization

open Polynomial NodalConductor

noncomputable section

variable (K : Type*) [Field K]

def nodeX : coordinates K := ⟨x K, Algebra.subset_adjoin (by simp)⟩
def nodeY : coordinates K := ⟨y K, Algebra.subset_adjoin (by simp)⟩

private def awayMapFor (c : coordinates K) :
    Localization.Away c →ₐ[K] Localization.Away c.val :=
  Localization.awayMapₐ (coordinates K).val c

private theorem awayMap_injective (c : coordinates K) : Function.Injective (awayMapFor K c) := by
  change Function.Injective (Localization.awayMap (coordinates K).val.toRingHom c)
  apply Localization.awayMap_injective_iff.mpr
  intro a ha
  have hz : a = 0 := Subtype.ext ha
  exact ⟨0, by rw [hz, mul_zero]⟩

private theorem awayMap_surjective (c : coordinates K)
    (hc : ∀ f : K[X], c.val * f ∈ coordinates K) :
    Function.Surjective (awayMapFor K c) := by
  change Function.Surjective (Localization.awayMap (coordinates K).val.toRingHom c)
  apply Localization.awayMap_surjective_iff.mpr
  intro a
  refine ⟨⟨c.val * a, hc a⟩, 1, ?_⟩
  change c.val * a = c.val ^ 1 * a
  rw [pow_one]

/-- Localizing at an actual conductor element makes the normalization an isomorphism. -/
def normalizationAwayConductor (c : coordinates K)
    (hc : ∀ f : K[X], c.val * f ∈ coordinates K) :
    Localization.Away c ≃ₐ[K] Localization.Away c.val :=
  AlgEquiv.ofBijective (awayMapFor K c) ⟨awayMap_injective K c, awayMap_surjective K c hc⟩

def awayMap : Localization.Away (nodeX K) →ₐ[K] Localization.Away (x K) :=
  awayMapFor K (nodeX K)

/-- The open complement of the node is the polynomial line localized at t² − 1. -/
def normalizationEquiv :
    Localization.Away (nodeX K) ≃ₐ[K] Localization.Away (x K) :=
  normalizationAwayConductor K (nodeX K) (x_mul_mem_coordinates K)

/-- The overlap of the Y and Z charts has parameter t with t(t²−1) inverted. -/
def overlapNormalizationEquiv :
    Localization.Away (nodeY K) ≃ₐ[K] Localization.Away (y K) :=
  normalizationAwayConductor K (nodeY K) (fun f => by
    change (x K * X) * f ∈ coordinates K
    rw [mul_assoc]
    exact x_mul_mem_coordinates K (X * f))

end
end ManuscriptAudit.NodalAwayNormalization

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalAwayNormalization.normalizationAwayConductor,
      ``ManuscriptAudit.NodalAwayNormalization.normalizationEquiv,
      ``ManuscriptAudit.NodalAwayNormalization.overlapNormalizationEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
