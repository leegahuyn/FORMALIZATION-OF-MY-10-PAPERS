import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper5ExtensionRecurrence
import PrimalitySheafVerification.ManuscriptAudit.CubicThreeTorsionCard

/-! The literal point-count recurrence over all split finite base fields. -/

namespace ManuscriptAudit.CubicSplitExtensionTraceRecurrence

open FiniteFieldPointCount CubicThreeTorsionCard
open CubicJacobiRoots CubicJacobiExtension CubicCharacterMultiplicity
open Paper5PrintedRecurrence Paper5ExtensionRecurrence LanglandsFirstMainLemma

noncomputable section

variable {F E : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Field E] [Fintype E] [DecidableEq E] [Algebra F E]

/-- The signed count on the actual projective centered cubic. -/
def signedTrace (A : F) : ℤ :=
  (Fintype.card F : ℤ) + 1 - (Nat.card (shortCubic (0 : F) A).toProjective.Point : ℤ)

private theorem char_ne_two {K : Type*} [Field K] (h : (2 : K) ≠ 0) : ringChar K ≠ 2 := by
  intro hr
  exact h ((ringChar.spec K 2).mpr (by simpa only [hr] using (dvd_rfl : (2 : ℕ) ∣ 2)))

private theorem exists_nontrivial_additive :
    ∃ ψ : AddChar F ℂ, ψ ≠ 1 := by
  let p := ringChar F
  letI : CharP F p := ringChar.charP F
  letI : Fact (Nat.Prime p) := ⟨CharP.char_is_prime F p⟩
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  obtain ⟨ψ, hψ⟩ := DavenportHasseJacobi.primeField_additiveCharacter (p := p)
  exact ⟨traceAddChar (ZMod p) F ψ, (traceAddChar_ne_one_iff (ZMod p) F ψ).mpr hψ⟩

/-- Actual signed counts over finite extensions satisfy the two-root recurrence over every
split finite base field of characteristic different from two and three. -/
theorem extension_trace_eq_recurrence {A : F}
    (h₂ : (2 : F) ≠ 0) (h₃ : (3 : F) ≠ 0) (hA : A ≠ 0)
    (hdiv : 3 ∣ Fintype.card F - 1) :
    signedTrace (algebraMap F E A) =
      recurrence (Fintype.card F) (signedTrace A) (Module.finrank F E) := by
  have hF := char_ne_two h₂
  have h₂E : (2 : E) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap F E)).mpr h₂
  have h₃E : (3 : E) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap F E)).mpr h₃
  have hAE : algebraMap F E A ≠ 0 := (map_ne_zero (algebraMap F E)).mpr hA
  obtain ⟨χ, hχ⟩ := exists_orderThree_character (F := F) hdiv
  obtain ⟨ψ, hψ⟩ := exists_nontrivial_additive (F := F)
  have hs := (projective_count_trace_complex hF (shortCubic_discriminant_ne_zero h₂ h₃ hA)).trans
    (cubicTraceSum_eq_neg_jacobiRoots hF hχ hA)
  have hsum : jacobiRoot χ A + jacobiRoot (χ ^ 2) A = (signedTrace A : ℂ) := by
    unfold signedTrace
    push_cast
    exact hs.symm
  have hrec := recurrence_cast_eq_root_powers (Fintype.card F) (signedTrace A) _ _
    hsum (jacobiRoots_product hF hχ hA) (Module.finrank F E)
  have hc := extension_actual_point_count (E := E) hF (char_ne_two h₂E) hχ hψ hA
    (shortCubic_discriminant_ne_zero h₂E h₃E hAE)
  rw [← hrec] at hc
  unfold signedTrace
  exact_mod_cast hc

end
end ManuscriptAudit.CubicSplitExtensionTraceRecurrence

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicSplitExtensionTraceRecurrence.extension_trace_eq_recurrence
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
