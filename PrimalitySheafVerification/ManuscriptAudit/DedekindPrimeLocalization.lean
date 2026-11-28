import Lean.Util.CollectAxioms
import Mathlib.RingTheory.ClassGroup.ExtendedHom
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Ideal.UFD

/-! Inverting a principal prime of a Dedekind domain preserves the ideal
class group. The map is extension of actual ideals along localization. -/

namespace ManuscriptAudit.DedekindPrimeLocalization

open IsLocalization.Away
open scoped nonZeroDivisors

noncomputable section

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (p : R) [Fact (Prime p)]

abbrev S := Localization.Away p

private theorem powers_regular : Submonoid.powers p ≤ R⁰ :=
  powers_le_nonZeroDivisors_of_noZeroDivisors (Fact.out : Prime p).ne_zero

private instance localizedDomain : IsDomain (S p) :=
  Localization.Away.isDomain (Fact.out : Prime p).ne_zero

private instance localizedDedekind : IsDedekindDomain (S p) :=
  IsLocalization.isDedekindDomain R (powers_regular p) (S p)

private theorem algebraMap_injective : Function.Injective (algebraMap R (S p)) :=
  IsLocalization.injective (M := Submonoid.powers p) (S p) (powers_regular p)

/-- The real extension homomorphism of class groups at the indicated principal open. -/
def classMap : ClassGroup R →* ClassGroup (S p) :=
  ClassGroup.map (algebraMap R (S p)) (algebraMap_injective p)

private theorem saturated_of_coprime {I : Ideal R}
    (hI : IsCoprime I (Ideal.span ({p} : Set R))) (x : R) (hx : p * x ∈ I) : x ∈ I := by
  have h1 : (1 : R) ∈ I ⊔ Ideal.span ({p} : Set R) := by
    rw [(Ideal.isCoprime_iff_sup_eq).mp hI]
    exact Ideal.mem_top
  obtain ⟨a, ha, b, hb, he⟩ := Submodule.mem_sup.mp h1
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hb
  have hh := I.add_mem (I.mul_mem_right x ha) (I.mul_mem_right c hx)
  have he' : a + p * c = 1 := by simpa only [hc] using he
  have e : a * x + (p * x) * c = x := by
    calc
      _ = a * x + (p * c) * x := by rw [mul_right_comm p x c]
      _ = (a + p * c) * x := by rw [add_mul]
      _ = x := by rw [he', one_mul]
  exact e ▸ hh

/-- A nonzero integral representative coprime to the inverted prime
is principal if its extension to the localization is principal. -/
theorem principal_of_localized_principal {I : Ideal R}
    (hI : I ≠ ⊥) (hc : IsCoprime I (Ideal.span ({p} : Set R)))
    (hP : (I.map (algebraMap R (S p))).IsPrincipal) : I.IsPrincipal := by
  have hp : Prime p := Fact.out
  have hIb : I.map (algebraMap R (S p)) ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective (algebraMap_injective p)).not.mpr hI
  obtain ⟨g, hg⟩ := hP
  have hg₀ : g ≠ 0 := fun h => hIb (by simp [hg, h])
  obtain ⟨a, n, ha, he⟩ := exists_reduced_fraction' p (S p) hg₀ hp.irreducible
  have hu : IsUnit (selfZPow p (S p) n) :=
    IsUnit.of_mul_eq_one (selfZPow p (S p) (-n)) (selfZPow_mul_neg p (S p) n)
  refine ⟨a, Ideal.eq_of_map_algebraMap_le (S p) p ?_ (saturated_of_coprime p hc) ?_⟩
  · simp [hg, Ideal.map_span, ← Ideal.span_singleton_mul_left_unit hu (algebraMap R (S p) a), he]
  · intro y hy
    rw [Ideal.mem_span_singleton] at hy ⊢
    exact (hp.left_dvd_or_dvd_right_of_dvd_mul hy).resolve_left ha

theorem classMap_surjective : Function.Surjective (classMap p) := by
  intro c
  obtain ⟨J, rfl⟩ := ClassGroup.mk0_surjective c
  let I := J.val.under R
  have hMap : I.map (algebraMap R (S p)) = J.val :=
    IsLocalization.map_under (Submonoid.powers p) (S p) J.val
  have hI : I ≠ ⊥ := by
    intro e
    have hJ : J.val ≠ ⊥ := mem_nonZeroDivisors_iff_ne_zero.mp J.property
    exact hJ (by simpa [e] using hMap.symm)
  refine ⟨ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩, ?_⟩
  rw [classMap, ClassGroup.map_mk0]
  exact congrArg ClassGroup.mk0 (Subtype.ext hMap)

theorem classMap_injective : Function.Injective (classMap p) := by
  apply (injective_iff_map_eq_one _).2
  intro c hc
  have hp : Prime p := Fact.out
  have hp₀ : (Ideal.span ({p} : Set R)) ≠ ⊥ :=
    fun h => hp.ne_zero (Ideal.span_singleton_eq_bot.mp h)
  obtain ⟨I, rfl, hCop⟩ := ClassGroup.exists_mk0_eq_and_isCoprime c hp₀
  have hI : I.val ≠ ⊥ := mem_nonZeroDivisors_iff_ne_zero.mp I.property
  have hImap : I.val.map (algebraMap R (S p)) ∈ (Ideal (S p))⁰ :=
    mem_nonZeroDivisors_iff_ne_zero.mpr
      ((Ideal.map_eq_bot_iff_of_injective (algebraMap_injective p)).not.mpr hI)
  have h₁ : ClassGroup.mk0 ⟨I.val.map (algebraMap R (S p)), hImap⟩ = 1 := by
    simpa only [classMap, ClassGroup.map_mk0] using hc
  exact (ClassGroup.mk0_eq_one_iff I.property).2
    (principal_of_localized_principal p hI hCop ((ClassGroup.mk0_eq_one_iff hImap).1 h₁))

/-- The actual class group isomorphism at an inverted principal prime. -/
def classEquiv : ClassGroup R ≃* ClassGroup (S p) :=
  MulEquiv.ofBijective (classMap p) ⟨classMap_injective p, classMap_surjective p⟩

end

end ManuscriptAudit.DedekindPrimeLocalization

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.DedekindPrimeLocalization.principal_of_localized_principal,
      ``ManuscriptAudit.DedekindPrimeLocalization.classMap_surjective,
      ``ManuscriptAudit.DedekindPrimeLocalization.classMap_injective,
      ``ManuscriptAudit.DedekindPrimeLocalization.classEquiv] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
