import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Localization.Away.Basic
import PrimalitySheafVerification.ManuscriptAudit.DedekindInverseIdealAlgebra

/-! Principal localizations of the actual inverse-ideal algebra
identify with those of the original ring on the complement of the ideal. -/

namespace ManuscriptAudit.DedekindInverseIdealLocalization

open DedekindInverseIdealAlgebra (inverseIdeal outsideAlgebra exists_numerator)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (A K : Type u) [CommRing A] [IsDedekindDomain A] [Field K]
  [Algebra A K] [IsFractionRing A K]

private theorem exists_power_numerator (I : Ideal A) (hI : I ≠ ⊥) {a : A} (ha : a ∈ I)
    (ha₀ : a ≠ 0) (y : outsideAlgebra A K I) :
    ∃ (n : ℕ) (d : A), (y : K) * algebraMap A K a ^ n = algebraMap A K d := by
  let S := Localization.Away a
  have h₀ : algebraMap A K a ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective A K).ne ha₀
  have hu : IsUnit ((Algebra.ofId A K) a) := IsUnit.mk0 _ h₀
  let j : S →ₐ[A] K := IsLocalization.Away.liftAlgHom a (f := Algebra.ofId A K) hu
  have hj (x : A) : j (algebraMap A S x) = algebraMap A K x :=
    IsLocalization.Away.lift_eq a hu x
  have hLe : outsideAlgebra A K I ≤ j.range := by
    apply Algebra.adjoin_le
    intro x hx
    obtain ⟨b, hb⟩ := exists_numerator A K I hI ha hx
    let a' : Submonoid.powers a := ⟨a, ⟨1, pow_one a⟩⟩
    let w := IsLocalization.mk' S b a'
    refine ⟨w, ?_⟩
    change j w = x
    apply mul_right_cancel₀ h₀
    calc
      _ = j (w * algebraMap A S a) := by rw [map_mul, hj]
      _ = j (algebraMap A S b) := congrArg j (IsLocalization.mk'_spec S b a')
      _ = _ := (hj b).trans hb
  obtain ⟨w, hw⟩ := hLe y.property
  have hw' : j w = (y : K) := hw
  obtain ⟨n, d, hd⟩ := IsLocalization.Away.surj a w
  refine ⟨n, d, ?_⟩
  have he := congrArg j hd
  rw [map_mul, map_pow, hj, hj, hw'] at he
  exact he

set_option maxHeartbeats 2000000 in
/-- On each nonempty principal open contained in the ideal's
complement, the actual new stage is literally the ordinary localization. -/
theorem isLocalization_away (I : Ideal A) (hI : I ≠ ⊥) {a : A} (ha : a ∈ I) (ha₀ : a ≠ 0) :
    IsLocalization.Away a (Localization.Away (algebraMap A (outsideAlgebra A K I) a)) := by
  let G := outsideAlgebra A K I
  let aG := algebraMap A G a
  let Z := Localization.Away aG
  have hk (x : A) : algebraMap A Z x = algebraMap G Z (algebraMap A G x) :=
    IsScalarTower.algebraMap_apply A G Z x
  apply IsLocalization.Away.mk a
  · rw [hk]
    exact IsLocalization.Away.algebraMap_isUnit aG
  · intro z
    obtain ⟨n, x, hx⟩ := IsLocalization.Away.surj aG z
    obtain ⟨m, d, hd⟩ := exists_power_numerator A K I hI ha ha₀ x
    have hd' : x * aG ^ m = algebraMap A G d := Subtype.val_injective hd
    refine ⟨n + m, d, ?_⟩
    calc
      _ = (z * algebraMap G Z aG ^ n) * algebraMap G Z aG ^ m := by
        rw [hk, pow_add, mul_assoc]
      _ = _ := by rw [hx, ← map_pow, ← map_mul, hd', ← hk]
  · intro x y h
    have h' : algebraMap G Z (algebraMap A G x) = algebraMap G Z (algebraMap A G y) := by
      change algebraMap A Z x = algebraMap A Z y at h
      exact (hk x).symm.trans (h.trans (hk y))
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq aG h'
    refine ⟨n, ?_⟩
    have hAG : Function.Injective (algebraMap A G) := fun _ _ e ↦
      (IsFractionRing.injective A K) (congrArg Subtype.val e)
    apply hAG
    simp only [map_mul, map_pow]
    exact hn

end
end ManuscriptAudit.DedekindInverseIdealLocalization

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.DedekindInverseIdealLocalization.isLocalization_away
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
