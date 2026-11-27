import Lean.Util.CollectAxioms
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassFrobeniusModTwo

/-! Finite additive order-four detection and the trace-zero square relation modulo four. -/

namespace ManuscriptAudit.FourTorsionDeterminantTools

open Polynomial WeierstrassFrobeniusModTwo

noncomputable section

/-- A finite group having at most four two-torsion points and order divisible by eight has order-four torsion. -/
theorem exists_orderFour {G : Type*} [AddCommGroup G] [Finite G]
    (hcard : 8 ∣ Nat.card G)
    (hker : Nat.card (nsmulAddMonoidHom (2 : ℕ) : G →+ G).ker ≤ 4) :
    ∃ P : G, (4 : ℕ) • P = 0 ∧ (2 : ℕ) • P ≠ 0 := by
  let f : G →+ G := nsmulAddMonoidHom 2
  have hCard : Nat.card G = Nat.card f.range * Nat.card f.ker := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker,
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv]
  have hEven : 2 ∣ Nat.card f.range := by
    by_contra hOdd
    have hCoprime : (8 : ℕ).Coprime (Nat.card f.range) :=
      ((Nat.prime_two.coprime_iff_not_dvd).mpr hOdd).pow_left 3
    have hd : 8 ∣ Nat.card f.ker := hCoprime.dvd_of_dvd_mul_left (by rwa [← hCard])
    have hle : 8 ≤ Nat.card f.ker := Nat.le_of_dvd Nat.card_pos hd
    change Nat.card f.ker ≤ 4 at hker
    omega
  obtain ⟨Q, hQ₀, hQ₂⟩ := (two_dvd_card_iff_nonzero_two_torsion (↥f.range)).mp hEven
  obtain ⟨P, hP⟩ := Q.property
  change (2 : ℕ) • P = (Q : G) at hP
  refine ⟨P, ?_, ?_⟩
  · rw [show (4 : ℕ) = 2 * 2 by decide, mul_nsmul', hP]
    exact congrArg (fun x : ↥f.range => (x : G)) hQ₂
  · rw [hP]
    exact fun h => hQ₀ (Subtype.ext h)

/-- Cayley–Hamilton forces the square of a trace-zero two-dimensional operator to be scalar. -/
theorem square_of_trace_zero {R V : Type*} [CommRing R] [Nontrivial R] [AddCommGroup V] [Module R V]
    (B : Module.Basis (Fin 2) R V) (F : Module.End R V)
    (hTrace : LinearMap.trace R V F = 0) :
    F ^ 2 = -(LinearMap.det F) • (1 : Module.End R V) := by
  letI : Module.Finite R V := Module.Finite.of_basis B
  letI : Module.Free R V := Module.Free.of_basis B
  have hchar : F.charpoly = X ^ 2 + C (LinearMap.det F) := by
    rw [← LinearMap.charpoly_toMatrix F B, Matrix.charpoly_fin_two,
      ← LinearMap.trace_eq_matrix_trace R B, LinearMap.det_toMatrix B, hTrace,
      map_zero, zero_mul, sub_zero]
  have h := LinearMap.aeval_self_charpoly F
  rw [hchar] at h
  simp only [map_add, map_pow, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one] at h
  rw [neg_smul]
  exact eq_neg_of_add_eq_zero_left h

theorem square_apply_of_trace_zero {R V : Type*} [CommRing R] [Nontrivial R] [AddCommGroup V] [Module R V]
    (B : Module.Basis (Fin 2) R V) (F : Module.End R V)
    (hTrace : LinearMap.trace R V F = 0) (P : V) :
    F (F P) = -(LinearMap.det F) • P := by
  have h := square_of_trace_zero B F hTrace
  rw [pow_two] at h
  exact congrArg (fun f : Module.End R V => f P) h

/-- The determinant of a linear automorphism over Z/4 is one or three. -/
theorem determinant_cases {V : Type*} [AddCommGroup V] [Module (ZMod 4) V]
    (F : V ≃ₗ[ZMod 4] V) :
    LinearMap.det F.toLinearMap = 1 ∨ LinearMap.det F.toLinearMap = 3 := by
  have hCases : ∀ a b : ZMod 4, a * b = 1 → a = 1 ∨ a = 3 := by decide
  let u := LinearEquiv.det F
  have hProd : (u : ZMod 4) * ((u⁻¹ : (ZMod 4)ˣ) : ZMod 4) = 1 :=
    congrArg (fun w : (ZMod 4)ˣ => (w : ZMod 4)) (mul_inv_cancel u)
  simpa only [u, LinearEquiv.coe_det] using hCases _ _ hProd

end
end ManuscriptAudit.FourTorsionDeterminantTools

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.FourTorsionDeterminantTools.exists_orderFour,
      ``ManuscriptAudit.FourTorsionDeterminantTools.square_of_trace_zero,
      ``ManuscriptAudit.FourTorsionDeterminantTools.square_apply_of_trace_zero,
      ``ManuscriptAudit.FourTorsionDeterminantTools.determinant_cases] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
