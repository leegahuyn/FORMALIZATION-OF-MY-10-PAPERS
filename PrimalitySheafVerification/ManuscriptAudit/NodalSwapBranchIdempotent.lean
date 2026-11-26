import Lean.Util.CollectAxioms
import Mathlib.Algebra.GroupWithZero.Idempotent
import PrimalitySheafVerification.ManuscriptAudit.NodalSwapCoverEtale

/-! On the normalized swap cover, its two component labels are reversed
when the parameter moves from t=1 to t=-1 over a single conductor lift. -/

namespace ManuscriptAudit.NodalSwapBranchIdempotent

open Polynomial NodalConductor NodalSwapCover NodalSwapCoverEtale
open scoped TensorProduct

noncomputable section

universe u
variable (K : Type u) [Field K]

abbrev A := coordinates K
abbrev B := Polynomial K
abbrev E := B K ⊗[A K] Cover K

/-- The element with value t on the first polynomial line and -t on the
second, which satisfies the crossed branch identifications. -/
def skew : Cover K := ⟨(X, -X), by
  change ((X : B K).eval 1 = (-X : B K).eval (-1)) ∧
    ((X : B K).eval (-1) = (-X : B K).eval 1)
  simp⟩

def t : E K := Polynomial.X ⊗ₜ[A K] (1 : Cover K)
def z : E K := (1 : B K) ⊗ₜ[A K] skew K

def idempotent (h2 : (2 : K) ≠ 0) : E K :=
  (normalizationRecovery K h2).symm (1, 0)

private theorem recovery_idempotent (h2 : (2 : K) ≠ 0) :
    normalizationRecovery K h2 (idempotent K h2) = (1, 0) :=
  (normalizationRecovery K h2).apply_symm_apply _

theorem idempotent_mul (h2 : (2 : K) ≠ 0) :
    idempotent K h2 * idempotent K h2 = idempotent K h2 := by
  apply (normalizationRecovery K h2).injective
  rw [map_mul, recovery_idempotent]
  ext <;> simp

private theorem recovery_t (h2 : (2 : K) ≠ 0) :
    normalizationRecovery K h2 (t K) = (Polynomial.X, Polynomial.X) := by
  change normalizationExtension K (Polynomial.X ⊗ₜ[A K] (1 : Cover K)) = _
  rw [normalizationExtension, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
  rfl

private theorem recovery_z (h2 : (2 : K) ≠ 0) :
    normalizationRecovery K h2 (z K) = (Polynomial.X, -Polynomial.X) := by
  change normalizationExtension K ((1 : B K) ⊗ₜ[A K] skew K) = _
  rw [normalizationExtension, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  rfl

/-- The one skew coordinate records the branch parameter multiplied by the
sign of the actual component idempotent. -/
theorem relation (h2 : (2 : K) ≠ 0) :
    z K = (2 * idempotent K h2 - 1) * t K := by
  apply (normalizationRecovery K h2).injective
  rw [map_mul, map_sub, map_mul, map_one, map_ofNat,
    recovery_z, recovery_t, recovery_idempotent]
  ext <;> simp <;> ring

private theorem residue_two_ne_zero (h2 : (2 : K) ≠ 0) (P : PrimeSpectrum (E K)) :
    (2 : E K ⧸ P.asIdeal) ≠ 0 := by
  letI : IsDomain (E K ⧸ P.asIdeal) := (Ideal.Quotient.isDomain_iff_prime _).mpr P.isPrime
  let f : K →+* E K ⧸ P.asIdeal := (Ideal.Quotient.mk P.asIdeal).comp
    ((Algebra.TensorProduct.includeLeft : B K →ₐ[A K] E K).toRingHom.comp Polynomial.C)
  have ht := (map_ne_zero_iff f f.injective).mpr h2
  simpa only [map_ofNat] using ht

/-- At the positive branch, the cover coordinate equals 1 precisely on
the first polynomial component. -/
theorem positive_branch_label (h2 : (2 : K) ≠ 0) (P : PrimeSpectrum (E K))
    (ht : t K - 1 ∈ P.asIdeal) :
    z K - 1 ∈ P.asIdeal ↔ idempotent K h2 ∉ P.asIdeal := by
  letI : IsDomain (E K ⧸ P.asIdeal) := (Ideal.Quotient.isDomain_iff_prime _).mpr P.isPrime
  let q := Ideal.Quotient.mk P.asIdeal
  have hqt : q (t K) = 1 := by
    have h : q (t K - 1) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ht
    rwa [map_sub, map_one, sub_eq_zero] at h
  have he : IsIdempotentElem (q (idempotent K h2)) :=
    (show IsIdempotentElem (idempotent K h2) from idempotent_mul K h2).map q
  have hqz : q (z K - 1) = 2 * (q (idempotent K h2) - 1) := by
    rw [relation K h2, map_sub, map_mul, map_sub, map_mul, map_ofNat, map_one, hqt]
    ring
  rw [← Ideal.Quotient.eq_zero_iff_mem, hqz, ← Ideal.Quotient.eq_zero_iff_mem]
  rw [mul_eq_zero, or_iff_right (residue_two_ne_zero K h2 P), sub_eq_zero]
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp he with h | h <;> simp [h]

/-- At the negative branch, the same cover coordinate equals 1 precisely
on the other component. -/
theorem negative_branch_label (h2 : (2 : K) ≠ 0) (P : PrimeSpectrum (E K))
    (ht : t K + 1 ∈ P.asIdeal) :
    z K - 1 ∈ P.asIdeal ↔ idempotent K h2 ∈ P.asIdeal := by
  letI : IsDomain (E K ⧸ P.asIdeal) := (Ideal.Quotient.isDomain_iff_prime _).mpr P.isPrime
  let q := Ideal.Quotient.mk P.asIdeal
  have hqt : q (t K) = -1 := by
    have h : q (t K + 1) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ht
    rw [map_add, map_one] at h
    exact eq_neg_of_add_eq_zero_left h
  have hqz : q (z K - 1) = -(2 * q (idempotent K h2)) := by
    rw [relation K h2, map_sub, map_mul, map_sub, map_mul, map_ofNat, map_one, hqt]
    ring
  rw [← Ideal.Quotient.eq_zero_iff_mem, hqz, neg_eq_zero,
    mul_eq_zero, or_iff_right (residue_two_ne_zero K h2 P), ← Ideal.Quotient.eq_zero_iff_mem]

end
end ManuscriptAudit.NodalSwapBranchIdempotent

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalSwapBranchIdempotent.relation,
      ``ManuscriptAudit.NodalSwapBranchIdempotent.positive_branch_label,
      ``ManuscriptAudit.NodalSwapBranchIdempotent.negative_branch_label] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
