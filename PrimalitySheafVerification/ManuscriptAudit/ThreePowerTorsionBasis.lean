import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.Pi
import PrimalitySheafVerification.ManuscriptAudit.ThreePowerTorsionIndependent

/-! Genuine coordinates from two lifts of a basis of order-three points. -/

namespace ManuscriptAudit.ThreePowerTorsionBasis

open TorsionFrobeniusModule

noncomputable section

variable (G : Type*) [AddCommGroup G]

abbrev Level (n : ℕ) := Torsion (3 ^ n) G

/-- Lifts of the two order-three basis vectors form a basis whenever the level has the expected size. -/
def equivOfLifts (B : Module.Basis (Fin 2) (ZMod 3) (Torsion 3 G))
    (n : ℕ) (hCard : Nat.card (Level G (n + 1)) = 9 ^ (n + 1))
    (P Q : Level G (n + 1))
    (hP : (3 ^ n : ℕ) • (P : G) = (B 0 : G))
    (hQ : (3 ^ n : ℕ) • (Q : G) = (B 1 : G)) :
    (ZMod (3 ^ (n + 1)) × ZMod (3 ^ (n + 1))) ≃ₗ[ZMod (3 ^ (n + 1))] Level G (n + 1) := by
  classical
  let R := ZMod (3 ^ (n + 1))
  let V := Level G (n + 1)
  let F : (R × R) →ₗ[R] V :=
    (LinearMap.fst R R R).smulRight P + (LinearMap.snd R R R).smulRight Q
  letI : NeZero (3 ^ (n + 1) : ℕ) := ⟨pow_ne_zero _ (by decide : (3 : ℕ) ≠ 0)⟩
  have hzero (a : R × R) (ha : F a = 0) : a = 0 := by
    have h₁ : a.1 • P = a.1.val • P := by
      calc
        _ = (a.1.val : R) • P := congrArg (fun c : R => c • P) (ZMod.natCast_zmod_val a.1).symm
        _ = _ := by rw [Nat.cast_smul_eq_nsmul]
    have h₂ : a.2 • Q = a.2.val • Q := by
      calc
        _ = (a.2.val : R) • Q := congrArg (fun c : R => c • Q) (ZMod.natCast_zmod_val a.2).symm
        _ = _ := by rw [Nat.cast_smul_eq_nsmul]
    change a.1 • P + a.2 • Q = 0 at ha
    rw [h₁, h₂] at ha
    have har : a.1.val • (P : G) + a.2.val • (Q : G) = 0 :=
      congrArg (fun g : V => (g : G)) ha
    obtain ⟨h₁z, h₂z⟩ := ThreePowerTorsionIndependent.nsmul_relation_unique B n
      (P : G) (Q : G) hP hQ a.1.val a.2.val (ZMod.val_lt a.1) (ZMod.val_lt a.2) har
    refine Prod.ext ?_ ?_
    · change a.1 = 0
      rw [← ZMod.natCast_zmod_val a.1, h₁z, Nat.cast_zero]
    · change a.2 = 0
      rw [← ZMod.natCast_zmod_val a.2, h₂z, Nat.cast_zero]
  have hInjective : Function.Injective F := by
    intro a b hab
    have he : F (a - b) = 0 := by rw [map_sub, hab, sub_self]
    exact sub_eq_zero.mp (hzero _ he)
  have hV : Nat.card V = 9 ^ (n + 1) := hCard
  letI : Finite V := Nat.finite_of_card_ne_zero (by rw [hV]; exact pow_ne_zero _ (by decide : (9 : ℕ) ≠ 0))
  letI : Fintype V := Fintype.ofFinite _
  have hR : Nat.card R = 3 ^ (n + 1) := by
    change Nat.card (ZMod (3 ^ (n + 1))) = _
    rw [Nat.card_eq_fintype_card, ZMod.card]
  have hSource : Nat.card (R × R) = 9 ^ (n + 1) := by
    rw [Nat.card_prod, hR, ← mul_pow, show (3 : ℕ) * 3 = 9 by decide]
  have hF : Fintype.card (R × R) = Fintype.card V := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hSource, hV]
  exact LinearEquiv.ofBijective F ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨hInjective, hF⟩)

theorem equivOfLifts_apply (B : Module.Basis (Fin 2) (ZMod 3) (Torsion 3 G))
    (n : ℕ) (hCard : Nat.card (Level G (n + 1)) = 9 ^ (n + 1))
    (P Q : Level G (n + 1))
    (hP : (3 ^ n : ℕ) • (P : G) = (B 0 : G))
    (hQ : (3 ^ n : ℕ) • (Q : G) = (B 1 : G))
    (r : ZMod (3 ^ (n + 1)) × ZMod (3 ^ (n + 1))) :
    equivOfLifts G B n hCard P Q hP hQ r = r.1 • P + r.2 • Q := rfl

end
end ManuscriptAudit.ThreePowerTorsionBasis

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.ThreePowerTorsionBasis.equivOfLifts,
      ``ManuscriptAudit.ThreePowerTorsionBasis.equivOfLifts_apply] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
