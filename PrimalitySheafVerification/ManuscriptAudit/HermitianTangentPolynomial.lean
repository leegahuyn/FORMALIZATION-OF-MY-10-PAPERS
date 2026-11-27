import Lean.Util.CollectAxioms
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Ring

/-! The exact tangent elimination identity for the affine Hermitian curve. -/

namespace ManuscriptAudit.HermitianTangentPolynomial

open Polynomial

noncomputable section

variable (E : Type*) [Field E] [Fintype E]

/-- The Frobenius tangent equation factors with multiplicities q and one. -/
theorem tangent_factorization (R : Type*) [CommRing R] [Algebra E R]
    (u v X : R)
    (h : u ^ (Fintype.card E + 1) + v ^ (Fintype.card E + 1) = 1) :
    let q := Fintype.card E
    v ^ (q * (q + 1)) * (X ^ (q + 1) - 1) + (1 - u ^ q * X) ^ (q + 1) =
      (X - u) ^ q * (X - u ^ (q * q)) := by
  let q := Fintype.card E
  let F := FiniteField.frobeniusAlgHom E R
  change v ^ (q * (q + 1)) * (X ^ (q + 1) - 1) + (1 - u ^ q * X) ^ (q + 1) =
    (X - u) ^ q * (X - u ^ (q * q))
  have hSub (a b : R) : (a - b) ^ q = a ^ q - b ^ q := map_sub F a b
  have hBin : (1 - u ^ q * X) ^ q = 1 - u ^ (q * q) * X ^ q := by
    rw [hSub, one_pow, mul_pow, ← pow_mul]
  have hf : (u ^ (q + 1)) ^ q + (v ^ (q + 1)) ^ q = 1 := by
    have he := congrArg F h
    rw [map_add, map_one] at he
    exact he
  have hu : (u ^ (q + 1)) ^ q = u ^ (q * q) * u ^ q := by
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  have hv : (v ^ (q + 1)) ^ q = v ^ (q * (q + 1)) := by
    rw [← pow_mul, Nat.mul_comm (q + 1) q]
  rw [hu, hv] at hf
  have hV : v ^ (q * (q + 1)) = 1 - u ^ (q * q) * u ^ q :=
    (eq_sub_iff_add_eq).mpr ((add_comm _ _).trans hf)
  rw [pow_succ X q, pow_succ (1 - u ^ q * X) q, hBin, hSub X u, hV]
  ring

/-- In the polynomial coordinate this is the literal power-factorization after eliminating the tangent. -/
theorem polynomial_elimination (K : Type*) [Field K] [Algebra E K] (u v : K)
    (h : u ^ (Fintype.card E + 1) + v ^ (Fintype.card E + 1) = 1) :
    let q := Fintype.card E
    C (v ^ (q * (q + 1))) * ((X : K[X]) ^ (q + 1) - 1) +
      (1 - C (u ^ q) * X) ^ (q + 1) =
      (X - C u) ^ q * (X - C (u ^ (q * q))) := by
  let q := Fintype.card E
  have hC : (C u : K[X]) ^ (q + 1) + C v ^ (q + 1) = 1 := by
    rw [← map_pow, ← map_pow, ← map_add, h, map_one]
  have he := tangent_factorization E (K[X]) (C u) (C v) X hC
  simpa only [← map_pow] using he

end
end ManuscriptAudit.HermitianTangentPolynomial

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.HermitianTangentPolynomial.tangent_factorization,
      ``ManuscriptAudit.HermitianTangentPolynomial.polynomial_elimination] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
