import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.Basis.Fin
import PrimalitySheafVerification.ManuscriptAudit.TorsionFrobeniusModule

/-! Independent lifts of a basis of order-three points at higher powers of three. -/

namespace ManuscriptAudit.ThreePowerTorsionIndependent

open TorsionFrobeniusModule

noncomputable section

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

variable {G : Type*} [AddCommGroup G]

private theorem nsmul_commute (a b : ℕ) (P : G) : a • (b • P) = b • (a • P) := by
  rw [← mul_nsmul', mul_nsmul]

private theorem three_dvd_coefficients
    (B : Module.Basis (Fin 2) (ZMod 3) (Torsion 3 G)) (a b : ℕ)
    (h : a • (B 0 : G) + b • (B 1 : G) = 0) :
    3 ∣ a ∧ 3 ∣ b := by
  have hT : (a : ZMod 3) • B 0 + (b : ZMod 3) • B 1 = 0 := by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    exact Subtype.ext h
  have h₀ := congrArg (fun P : Torsion 3 G => B.repr P (0 : Fin 2)) hT
  have h₁ := congrArg (fun P : Torsion 3 G => B.repr P (1 : Fin 2)) hT
  have ha : (a : ZMod 3) = 0 := by
    simpa [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul] using h₀
  have hb : (b : ZMod 3) = 0 := by
    simpa [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul] using h₁
  exact ⟨(ZMod.natCast_eq_zero_iff a 3).mp ha, (ZMod.natCast_eq_zero_iff b 3).mp hb⟩

/-- A relation among two lifts of a basis of order-three points has zero coefficients modulo 3^(n+1). -/
theorem nsmul_relation_unique (B : Module.Basis (Fin 2) (ZMod 3) (Torsion 3 G))
    (n : ℕ) (P Q : G) (hP : (3 ^ n : ℕ) • P = (B 0 : G))
    (hQ : (3 ^ n : ℕ) • Q = (B 1 : G)) (a b : ℕ)
    (ha : a < 3 ^ (n + 1)) (hb : b < 3 ^ (n + 1))
    (h : a • P + b • Q = 0) : a = 0 ∧ b = 0 := by
  induction n generalizing P Q a b with
  | zero =>
    simp only [pow_zero, one_nsmul] at hP hQ
    rw [hP, hQ] at h
    obtain ⟨h₀, h₁⟩ := three_dvd_coefficients B a b h
    rw [Nat.dvd_iff_mod_eq_zero] at h₀ h₁
    change a < 3 at ha
    change b < 3 at hb
    omega
  | succ n ih =>
    have ht := congrArg (fun x : G => (3 ^ (n + 1) : ℕ) • x) h
    change (3 ^ (n + 1) : ℕ) • (a • P + b • Q) = (3 ^ (n + 1) : ℕ) • 0 at ht
    rw [nsmul_add, nsmul_commute _ a P, nsmul_commute _ b Q, hP, hQ, nsmul_zero] at ht
    obtain ⟨haDiv, hbDiv⟩ := three_dvd_coefficients B a b ht
    rw [Nat.dvd_iff_mod_eq_zero] at haDiv hbDiv
    have ha₃ : a = a / 3 * 3 := by omega
    have hb₃ : b = b / 3 * 3 := by omega
    have hrel : (a / 3) • ((3 : ℕ) • P) + (b / 3) • ((3 : ℕ) • Q) = 0 := by
      rw [← mul_nsmul', ← mul_nsmul', ← ha₃, ← hb₃]
      exact h
    have hP' : (3 ^ n : ℕ) • ((3 : ℕ) • P) = (B 0 : G) := by
      rw [← mul_nsmul', ← pow_succ]
      exact hP
    have hQ' : (3 ^ n : ℕ) • ((3 : ℕ) • Q) = (B 1 : G) := by
      rw [← mul_nsmul', ← pow_succ]
      exact hQ
    have ha' : a / 3 < 3 ^ (n + 1) := by
      rw [pow_succ (3 : ℕ) (n + 1)] at ha
      omega
    have hb' : b / 3 < 3 ^ (n + 1) := by
      rw [pow_succ (3 : ℕ) (n + 1)] at hb
      omega
    obtain ⟨ha₀, hb₀⟩ := ih ((3 : ℕ) • P) ((3 : ℕ) • Q) hP' hQ'
      (a / 3) (b / 3) ha' hb' hrel
    omega

end
end ManuscriptAudit.ThreePowerTorsionIndependent

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.ThreePowerTorsionIndependent.nsmul_relation_unique
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
