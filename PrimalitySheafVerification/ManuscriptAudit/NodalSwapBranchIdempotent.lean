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

private theorem two_isUnit (h2 : (2 : K) ≠ 0) : IsUnit (2 : E K) := by
  let f : K →+* E K :=
    (Algebra.TensorProduct.includeLeft : B K →ₐ[A K] E K).toRingHom.comp Polynomial.C
  simpa only [map_ofNat] using (isUnit_iff_ne_zero.mpr h2).map f

section PrimeLabels

variable {R : Type*} [CommRing R] (P : Ideal R) [P.IsPrime]

private theorem mem_iff_of_sub_mem {a b : R} (h : a - b ∈ P) :
    a ∈ P ↔ b ∈ P :=
  ⟨fun ha => by simpa only [sub_sub_cancel] using P.sub_mem ha h,
    fun hb => by simpa only [sub_add_cancel] using P.add_mem h hb⟩

private theorem mul_two_mem_iff (h2 : IsUnit (2 : R)) (x : R) :
    2 * x ∈ P ↔ x ∈ P :=
  ⟨fun h => (show P.IsPrime from inferInstance).mem_or_mem h |>.resolve_left
      (P.notMem_of_isUnit h2),
    P.mul_mem_left _⟩

private theorem positiveLabel (h2 : IsUnit (2 : R)) (z e t : R)
    (h : z = (2 * e - 1) * t) (he : e * e = e) (ht : t - 1 ∈ P) :
    z - 1 ∈ P ↔ e ∉ P := by
  have hdi : (z - 1) - 2 * (e - 1) ∈ P := by
    rw [h, show (2 * e - 1) * t - 1 - 2 * (e - 1) = (2 * e - 1) * (t - 1) by ring]
    exact P.mul_mem_left _ ht
  rw [mem_iff_of_sub_mem P hdi, mul_two_mem_iff P h2]
  have hep : e * (e - 1) ∈ P := by
    rw [mul_sub, mul_one, he, sub_self]
    exact P.zero_mem
  constructor
  · intro h₁ h₂
    exact (show P.IsPrime from inferInstance).one_notMem
      (by simpa only [sub_sub_cancel] using P.sub_mem h₂ h₁)
  · intro h
    exact (show P.IsPrime from inferInstance).mem_or_mem hep |>.resolve_left h

private theorem negativeLabel (h2 : IsUnit (2 : R)) (z e t : R)
    (h : z = (2 * e - 1) * t) (ht : t + 1 ∈ P) :
    z - 1 ∈ P ↔ e ∈ P := by
  have hdi : (z - 1) - (-(2 * e)) ∈ P := by
    rw [h, show (2 * e - 1) * t - 1 - (-(2 * e)) = (2 * e - 1) * (t + 1) by ring]
    exact P.mul_mem_left _ ht
  rw [mem_iff_of_sub_mem P hdi, Ideal.neg_mem_iff, mul_two_mem_iff P h2]

end PrimeLabels

/-- At the positive branch, the cover coordinate equals 1 precisely on
the first polynomial component. -/
theorem positive_branch_label (h2 : (2 : K) ≠ 0) (P : PrimeSpectrum (E K))
    (ht : t K - 1 ∈ P.asIdeal) :
    z K - 1 ∈ P.asIdeal ↔ idempotent K h2 ∉ P.asIdeal := by
  letI : P.asIdeal.IsPrime := P.isPrime
  exact positiveLabel P.asIdeal (two_isUnit K h2) _ _ _ (relation K h2)
    (idempotent_mul K h2) ht

/-- At the negative branch, the same cover coordinate equals 1 precisely
on the other component. -/
theorem negative_branch_label (h2 : (2 : K) ≠ 0) (P : PrimeSpectrum (E K))
    (ht : t K + 1 ∈ P.asIdeal) :
    z K - 1 ∈ P.asIdeal ↔ idempotent K h2 ∈ P.asIdeal := by
  letI : P.asIdeal.IsPrime := P.isPrime
  exact negativeLabel P.asIdeal (two_isUnit K h2) _ _ _ (relation K h2) ht

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
