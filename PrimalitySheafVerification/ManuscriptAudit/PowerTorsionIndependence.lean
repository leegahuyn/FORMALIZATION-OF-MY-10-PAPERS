import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.Basis.Fin
import PrimalitySheafVerification.ManuscriptAudit.PowerTorsionLift

/-! Independence of two compatible lifted torsion generators at every level. -/

namespace ManuscriptAudit.PowerTorsionIndependence

open PowerTorsionTower PowerTorsionLift TorsionFrobeniusModule

noncomputable section

variable (m : ℕ) {G : Type*} [AddCommGroup G]

private theorem nsmul_comm (a b : ℕ) (P : G) :
    a • (b • P) = b • (a • P) := by
  rw [← mul_nsmul', ← mul_nsmul', Nat.mul_comm a b]

variable (B : Module.Basis (Fin 2) (ZMod (m ^ 1)) (PowerTorsion m G 1))

private theorem dvd_of_base_relation (a b : ℕ)
    (h : a • (B 0 : G) + b • (B 1 : G) = 0) : m ∣ a ∧ m ∣ b := by
  have he : a • B 0 + b • B 1 = 0 := Subtype.ext h
  have ha := congrArg (fun x : PowerTorsion m G 1 => B.repr x 0) he
  have hb := congrArg (fun x : PowerTorsion m G 1 => B.repr x 1) he
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 : (1 : Fin 2) ≠ 0 := h01.symm
  have ha' : (a : ZMod (m ^ 1)) = 0 := by
    simpa [map_add, map_nsmul, Finsupp.single_apply, h01, h10] using ha
  have hb' : (b : ZMod (m ^ 1)) = 0 := by
    simpa [map_add, map_nsmul, Finsupp.single_apply, h01, h10] using hb
  exact ⟨by simpa only [pow_one] using (ZMod.natCast_eq_zero_iff a (m ^ 1)).mp ha',
    by simpa only [pow_one] using (ZMod.natCast_eq_zero_iff b (m ^ 1)).mp hb'⟩

variable (hm : 0 < m)
variable (h : Function.Surjective (fun P : G => m • P))

/-- One coherent family of lifts for each element of the original two-element basis. -/
def generator (i : Fin 2) (n : ℕ) : PowerTorsion m G (n + 1) :=
  lifted m G h (B i) n

@[simp] theorem generator_transition (i : Fin 2) (n : ℕ) :
    transition m G (n + 1) (generator m B h i (n + 1)) = generator m B h i n :=
  transition_lifted m G h (B i) n

private theorem dvd_of_relation (n a b : ℕ)
    (he : a • (generator m B h 0 n : G) + b • (generator m B h 1 n : G) = 0) :
    m ∣ a ∧ m ∣ b := by
  have hScaled := congrArg (fun x : G => (m ^ n : ℕ) • x) he
  have h0 : (m ^ n : ℕ) • (generator m B h 0 n : G) = (B 0 : G) :=
    scale_lifted m G h (B 0) n
  have h1 : (m ^ n : ℕ) • (generator m B h 1 n : G) = (B 1 : G) :=
    scale_lifted m G h (B 1) n
  change (m ^ n : ℕ) • (a • (generator m B h 0 n : G) + b • (generator m B h 1 n : G)) =
    (m ^ n : ℕ) • (0 : G) at hScaled
  rw [nsmul_add, nsmul_zero, nsmul_comm (m ^ n) a, nsmul_comm (m ^ n) b, h0, h1] at hScaled
  exact dvd_of_base_relation m B a b hScaled

include hm in
theorem relation_unique (n a b : ℕ) (ha : a < m ^ (n + 1)) (hb : b < m ^ (n + 1))
    (he : a • (generator m B h 0 n : G) + b • (generator m B h 1 n : G) = 0) :
    a = 0 ∧ b = 0 := by
  induction n generalizing a b with
  | zero =>
    obtain ⟨da, db⟩ := dvd_of_relation m B h 0 a b he
    rw [pow_one] at ha hb
    exact ⟨Nat.eq_zero_of_dvd_of_lt da ha, Nat.eq_zero_of_dvd_of_lt db hb⟩
  | succ n ih =>
    obtain ⟨da, db⟩ := dvd_of_relation m B h (n + 1) a b he
    obtain ⟨a', ha'⟩ := da
    obtain ⟨b', hb'⟩ := db
    have ha'' : a' < m ^ (n + 1) := by
      apply (Nat.mul_lt_mul_left hm).mp
      simpa only [ha', pow_succ'] using ha
    have hb'' : b' < m ^ (n + 1) := by
      apply (Nat.mul_lt_mul_left hm).mp
      simpa only [hb', pow_succ'] using hb
    have h0 : m • (generator m B h 0 (n + 1) : G) = (generator m B h 0 n : G) :=
      congrArg (fun P : PowerTorsion m G (n + 1) => (P : G)) (generator_transition m B h 0 n)
    have h1 : m • (generator m B h 1 (n + 1) : G) = (generator m B h 1 n : G) :=
      congrArg (fun P : PowerTorsion m G (n + 1) => (P : G)) (generator_transition m B h 1 n)
    rw [ha', hb', Nat.mul_comm m a', Nat.mul_comm m b', mul_nsmul', mul_nsmul', h0, h1] at he
    obtain ⟨za, zb⟩ := ih a' b' ha'' hb'' he
    exact ⟨by rw [ha', za, mul_zero], by rw [hb', zb, mul_zero]⟩

end
end ManuscriptAudit.PowerTorsionIndependence

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.PowerTorsionIndependence.generator_transition,
      ``ManuscriptAudit.PowerTorsionIndependence.relation_unique] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
