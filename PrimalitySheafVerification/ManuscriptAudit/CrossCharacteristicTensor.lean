import Mathlib.Algebra.Module.NatInt
import Mathlib.Data.Int.GCD
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic

open scoped TensorProduct

namespace PrimalitySheafVerification.ManuscriptAudit

/-!
Paper 2, physical PDF p. 42, writes an ordinary tensor over the integers in
the definition of the derived detector. The theorem below applies degreewise
when the complex is represented by terms killed by the fiber characteristic
and the coefficient characteristic is coprime to it. A comparison with
the étale detector requires separate geometric and cohomological results.
-/

/-- Ordinary tensor products of modules with coprime annihilators vanish. -/
theorem paper2_tensor_subsingleton_of_coprime {p ℓ : ℕ} {M N : Type*}
    [AddCommGroup M] [AddCommGroup N] (hc : p.Coprime ℓ)
    (hM : ∀ x : M, (p : ℤ) • x = 0) (hN : ∀ y : N, (ℓ : ℤ) • y = 0) :
    Subsingleton (M ⊗[ℤ] N) := by
  have hbez : Nat.gcdA p ℓ * (p : ℤ) + Nat.gcdB p ℓ * (ℓ : ℤ) = 1 := by
    calc
      _ = ((p.gcd ℓ : ℕ) : ℤ) := by
        rw [mul_comm (Nat.gcdA p ℓ) (p : ℤ), mul_comm (Nat.gcdB p ℓ) (ℓ : ℤ)]
        exact (Nat.gcd_eq_gcd_ab p ℓ).symm
      _ = 1 := by rw [show p.gcd ℓ = 1 from hc, Nat.cast_one]
  have hzero (t : M ⊗[ℤ] N) : t = 0 := by
    induction t using TensorProduct.induction_on with
    | zero => rfl
    | tmul x y =>
      calc
        x ⊗ₜ[ℤ] y =
            ((Nat.gcdA p ℓ * (p : ℤ) + Nat.gcdB p ℓ * (ℓ : ℤ)) • x) ⊗ₜ[ℤ] y := by
          rw [hbez, one_smul]
        _ = 0 := by
          rw [add_smul, TensorProduct.add_tmul,
            mul_smul (Nat.gcdA p ℓ) (p : ℤ) x, hM x, smul_zero,
            TensorProduct.zero_tmul, zero_add]
          rw [mul_comm (Nat.gcdB p ℓ) (ℓ : ℤ), mul_smul,
            TensorProduct.smul_tmul (R := ℤ) (ℓ : ℤ), hN y, TensorProduct.tmul_zero]
    | add t s ht hs => rw [ht, hs, zero_add]
  exact ⟨fun t s => (hzero t).trans (hzero s).symm⟩

private theorem paper2_zmod_module_int_smul_zero (p : ℕ) {M : Type*} [AddCommGroup M]
    [Module (ZMod p) M] (x : M) : (p : ℤ) • x = 0 := by
  rw [← Int.cast_smul_eq_zsmul (ZMod p) (p : ℤ) x, Int.cast_natCast,
    ZMod.natCast_self, zero_smul]

/-- An ordinary change from a `ZMod p`-module to coprime `ZMod ℓ` coefficients vanishes. -/
theorem paper2_tensor_zmod_of_coprime {p ℓ : ℕ} {M : Type*} [AddCommGroup M]
    [Module (ZMod p) M] (hc : p.Coprime ℓ) : Subsingleton (M ⊗[ℤ] ZMod ℓ) :=
  paper2_tensor_subsingleton_of_coprime hc
    (paper2_zmod_module_int_smul_zero p) (paper2_zmod_module_int_smul_zero ℓ)

/-- Every abelian group killed by five has zero ordinary tensor with `ZMod 2`. -/
theorem paper2_tensor_zmod_two_of_five_torsion {M : Type*} [AddCommGroup M]
    (hM : ∀ x : M, (5 : ℤ) • x = 0) : Subsingleton (M ⊗[ℤ] ZMod 2) :=
  paper2_tensor_subsingleton_of_coprime (show Nat.Coprime 5 2 from by decide)
    hM (paper2_zmod_module_int_smul_zero 2)

/-- In particular this applies to every vector space over the field with five elements. -/
theorem paper2_tensor_five_vector_space_zmod_two {M : Type*} [AddCommGroup M]
    [Module (ZMod 5) M] : Subsingleton (M ⊗[ℤ] ZMod 2) :=
  paper2_tensor_zmod_of_coprime (show Nat.Coprime 5 2 from by decide)

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``paper2_tensor_subsingleton_of_coprime, ``paper2_tensor_zmod_of_coprime,
      ``paper2_tensor_zmod_two_of_five_torsion, ``paper2_tensor_five_vector_space_zmod_two] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"

end PrimalitySheafVerification.ManuscriptAudit
