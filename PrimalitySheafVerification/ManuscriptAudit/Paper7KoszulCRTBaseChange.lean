import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.NormNum

/-! A literal rank-one Koszul complex over the five-local integers loses
regularity after passage to the indicated CRT factor, with gcd(2,5)=1. -/

namespace ManuscriptAudit.Paper7KoszulCRTBaseChange

open CategoryTheory CategoryTheory.Limits

noncomputable section

private abbrev P : Ideal ℤ := Ideal.span ({(5 : ℤ)} : Set ℤ)

private instance : P.IsPrime :=
  (Ideal.span_singleton_prime (by norm_num : (5 : ℤ) ≠ 0)).mpr
    (Int.prime_iff_natAbs_prime.mpr (by exact Nat.prime_five))

abbrev R := Localization.AtPrime P
abbrev I : Ideal R := Ideal.span ({(5 : R)} : Set R)
abbrev S := R ⧸ I

def reduction : R →+* S := Ideal.Quotient.mk I

theorem parameter_in_maximal : (5 : R) ∈ IsLocalRing.maximalIdeal R := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal, ← map_ofNat (algebraMap ℤ R) 5]
  exact Ideal.mem_map_of_mem _ (Ideal.subset_span (by simp))

theorem parameter_ne_zero : (5 : R) ≠ 0 := by
  have hinj : Function.Injective (algebraMap ℤ R) :=
    (faithfulSMul_iff_algebraMap_injective ℤ R).mp inferInstance
  simpa only [map_ofNat, map_zero] using hinj.ne (by norm_num : (5 : ℤ) ≠ 0)

private theorem I_ne_top : I ≠ ⊤ := by
  have h : I ≤ IsLocalRing.maximalIdeal R :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr parameter_in_maximal)
  exact ne_top_of_le_ne_top
    (inferInstance : (IsLocalRing.maximalIdeal R).IsMaximal).ne_top h

private instance : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr I_ne_top

theorem reduction_parameter : reduction (5 : R) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

/-- The degree 2, 1, 0 segment of the genuine one-parameter Koszul complex. -/
abbrev rankOne (A : Type*) [CommRing A] (s : A) : ShortComplex (ModuleCat A) :=
  ShortComplex.mk (0 : ModuleCat.of A PUnit ⟶ ModuleCat.of A A)
    (ModuleCat.ofHom (s • (LinearMap.id : A →ₗ[A] A))) (by simp)

theorem regular_parameter : Function.Injective (fun x : R ↦ (5 : R) * x) := by
  letI : IsDomain R := IsLocalization.isDomain_of_local_atPrime inferInstance
  intro x y h
  exact mul_left_cancel₀ parameter_ne_zero h

theorem before_exact : (rankOne R 5).Exact := by
  apply (ShortComplex.moduleCat_exact_iff (rankOne R 5)).mpr
  intro x hx
  change R at x
  change (5 : R) * x = 0 at hx
  have h : (5 : R) * x = (5 : R) * 0 := by simpa using hx
  have hx0 := regular_parameter h
  exact ⟨0, by simpa [rankOne] using hx0.symm⟩

theorem after_not_exact : ¬ (rankOne S (reduction 5)).Exact := by
  intro h
  have hg : (rankOne S (reduction 5)).g (1 : S) = 0 := by
    change reduction 5 * 1 = 0
    rw [reduction_parameter, zero_mul]
  obtain ⟨x, hx⟩ := (ShortComplex.moduleCat_exact_iff (rankOne S (reduction 5))).mp h (1 : S) hg
  have h01 : (0 : S) = 1 := by simpa [rankOne] using hx
  exact zero_ne_one h01

/-- The actual degree-one homology vanishes before the listed base change
and is nonzero after it, in the coprime regime of the manuscript. -/
theorem crt_acyclicity_failure :
    Nat.Coprime 2 5 ∧
    IsZero (rankOne R 5).homology ∧
    ¬ IsZero (rankOne S (reduction 5)).homology :=
  ⟨by decide, (ShortComplex.exact_iff_isZero_homology _).1 before_exact,
    fun h ↦ after_not_exact ((ShortComplex.exact_iff_isZero_homology _).2 h)⟩

end
end ManuscriptAudit.Paper7KoszulCRTBaseChange

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.Paper7KoszulCRTBaseChange.parameter_in_maximal,
      ``ManuscriptAudit.Paper7KoszulCRTBaseChange.regular_parameter,
      ``ManuscriptAudit.Paper7KoszulCRTBaseChange.crt_acyclicity_failure] do
    let ax ← collectAxioms name
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
