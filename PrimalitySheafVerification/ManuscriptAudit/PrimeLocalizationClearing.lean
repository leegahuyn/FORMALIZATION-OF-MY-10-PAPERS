import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! A chosen lift in a stage's prime localization is represented by
a literal fraction after shrinking on both actual affine schemes. -/

namespace ManuscriptAudit.PrimeLocalizationClearing

noncomputable section

variable {D B : Type*} [CommRing D] [CommRing B]

/-- An equality of stage and chart sections in prime localizations
clears to an equality after inverting one element avoiding each prime. -/
theorem exists_cleared (g : D →+* B) (q : Ideal D) [q.IsPrime]
    (r : Ideal B) [r.IsPrime] (hqr : q = r.comap g)
    (v : Localization.AtPrime q) (z : B)
    (h : Localization.localRingHom q r g hqr v = algebraMap B (Localization.AtPrime r) z) :
    ∃ (a e : D) (t : B), e ∉ q ∧ t ∉ r ∧ t * g a = t * (g e * z) := by
  let S := Localization.AtPrime q
  let T := Localization.AtPrime r
  let f : S →+* T := Localization.localRingHom q r g hqr
  obtain ⟨a, e, he⟩ := IsLocalization.exists_mk'_eq q.primeCompl v
  have hv : f (IsLocalization.mk' S a e) = algebraMap B T z := by
    rw [he]
    exact h
  have hc : algebraMap B T (g a) = algebraMap B T (g (e : D) * z) := by
    calc
      _ = f (algebraMap D S a) := (Localization.localRingHom_to_map q r g hqr a).symm
      _ = f (IsLocalization.mk' S a e * algebraMap D S e) :=
        congrArg f (IsLocalization.mk'_spec S a e).symm
      _ = _ := by
        rw [map_mul, hv, Localization.localRingHom_to_map, map_mul]
        exact mul_comm _ _
  obtain ⟨t, ht⟩ := (IsLocalization.eq_iff_exists r.primeCompl T).mp hc
  exact ⟨a, e, t, e.property, t.property, ht⟩

end
end ManuscriptAudit.PrimeLocalizationClearing

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.PrimeLocalizationClearing.exists_cleared
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
