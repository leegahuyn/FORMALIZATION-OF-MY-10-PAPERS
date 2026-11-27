import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.NormNum

/-!
# Regularity at one actual stalk does not control other charts

On Spec(ℤ × ℤ), the section (3,0) is a regular nonunit at the prime
over (3) of the first component. The full rank-one Koszul first group
has the nonzero class (0,1). Its degree-two term is zero.
-/

namespace ManuscriptAudit.OneStalkKoszulCounterexample

open scoped BigOperators

noncomputable section

abbrev R := ℤ × ℤ

private abbrev P : Ideal ℤ := Ideal.span ({(3 : ℤ)} : Set ℤ)

private instance : P.IsPrime :=
  (Ideal.span_singleton_prime (by norm_num : (3 : ℤ) ≠ 0)).mpr
    (Nat.prime_iff_prime_int.mp Nat.prime_three)

abbrev firstPrime : Ideal R := P.comap (RingHom.fst ℤ ℤ)

local instance : firstPrime.IsPrime := inferInstance

abbrev stalkRing := Localization.AtPrime P

local instance : Algebra R stalkRing :=
  ((algebraMap ℤ stalkRing).comp (RingHom.fst ℤ ℤ)).toAlgebra

private theorem stalk_map_apply (x : R) :
    algebraMap R stalkRing x = algebraMap ℤ stalkRing x.1 := rfl

theorem actual_first_prime_localization : IsLocalization firstPrime.primeCompl stalkRing := by
  rw [IsLocalization.isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro y
    change IsUnit (algebraMap ℤ stalkRing y.val.1)
    exact IsLocalization.map_units stalkRing (⟨y.val.1, y.property⟩ : P.primeCompl)
  · intro z
    obtain ⟨⟨x, d⟩, hx⟩ := IsLocalization.surj P.primeCompl z
    exact ⟨⟨(x, 0), ⟨(d.val, 1), d.property⟩⟩, hx⟩
  · intro x y he
    change algebraMap ℤ stalkRing x.1 = algebraMap ℤ stalkRing y.1 at he
    obtain ⟨d, hd⟩ := IsLocalization.exists_of_eq (M := P.primeCompl) he
    refine ⟨⟨(d.val, 0), d.property⟩, Prod.ext hd ?_⟩
    change (0 : ℤ) * x.2 = 0 * y.2
    simp

def sectionValue : R := (3, 0)

theorem section_regular_at_first_stalk :
    Function.Injective (fun u : stalkRing => algebraMap R stalkRing sectionValue * u) ∧
      algebraMap R stalkRing sectionValue ∈ IsLocalRing.maximalIdeal stalkRing := by
  have h3 : (3 : stalkRing) ≠ 0 := by
    have h : Function.Injective (algebraMap ℤ stalkRing) :=
      (faithfulSMul_iff_algebraMap_injective ℤ stalkRing).mp inferInstance
    simpa only [map_ofNat, map_zero] using h.ne (by norm_num : (3 : ℤ) ≠ 0)
  have hm : (3 : stalkRing) ∈ IsLocalRing.maximalIdeal stalkRing := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, ← map_ofNat (algebraMap ℤ stalkRing) 3]
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span (by simp))
  have he : algebraMap R stalkRing sectionValue = (3 : stalkRing) := by
    rw [stalk_map_apply, sectionValue]
    norm_num
  rw [he]
  letI : IsDomain stalkRing := IsLocalization.isDomain_of_local_atPrime inferInstance
  exact ⟨fun _ _ h => mul_left_cancel₀ h3 h, hm⟩

def koszulDifferential : R →ₗ[R] R := sectionValue • LinearMap.id

abbrev koszulHOne := LinearMap.ker koszulDifferential

theorem koszulHOne_nonzero : Nontrivial koszulHOne := by
  let x : koszulHOne := ⟨(0, 1), by
    change sectionValue * (0, 1) = (0 : R)
    ext <;> norm_num [sectionValue]⟩
  refine ⟨x, 0, ?_⟩
  intro h
  have he := congrArg (fun u : koszulHOne => u.val.2) h
  norm_num [x] at he

end
end ManuscriptAudit.OneStalkKoszulCounterexample

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.OneStalkKoszulCounterexample.actual_first_prime_localization,
      ``ManuscriptAudit.OneStalkKoszulCounterexample.section_regular_at_first_stalk,
      ``ManuscriptAudit.OneStalkKoszulCounterexample.koszulHOne_nonzero] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
