import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Span.Basic
import PrimalitySheafVerification.ManuscriptAudit.PowerTorsionIndependence

/-! Two lifted basis vectors give compatible native free coordinates at every level. -/

namespace ManuscriptAudit.PowerTorsionCompatibleBasis

open PowerTorsionTower PowerTorsionIndependence TorsionFrobeniusModule

noncomputable section

variable (m : ℕ) (G : Type*) [AddCommGroup G]
variable (B : Module.Basis (Fin 2) (ZMod (m ^ 1)) (PowerTorsion m G 1))
variable (hm : 0 < m) (h : Function.Surjective (fun P : G => m • P))

private theorem first_card :
    Nat.card (Torsion m G) = m * m := by
  calc
    _ = Nat.card (PowerTorsion m G 1) := by simp only [PowerTorsion, pow_one]
    _ = Nat.card (Fin 2 → ZMod (m ^ 1)) := Nat.card_congr B.equivFun.toEquiv
    _ = _ := by rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin, pow_one, pow_two]

def zeroLevelEquiv :
    (ZMod (m ^ 0) × ZMod (m ^ 0)) ≃ₗ[ZMod (m ^ 0)] PowerTorsion m G 0 := by
  letI : Subsingleton (ZMod (m ^ 0) × ZMod (m ^ 0)) :=
    inferInstanceAs (Subsingleton (ZMod 1 × ZMod 1))
  have hz (P : PowerTorsion m G 0) : (P : G) = 0 := by
    simpa only [pow_zero, one_nsmul] using (mem_iff (m ^ 0) G _).mp P.property
  letI : Subsingleton (PowerTorsion m G 0) :=
    ⟨fun P Q => Subtype.ext ((hz P).trans (hz Q).symm)⟩
  exact LinearEquiv.ofBijective 0 ⟨fun x y _ => Subsingleton.elim x y,
    fun x => ⟨0, Subsingleton.elim _ x⟩⟩

private def positiveLevelEquiv (n : ℕ) :
    (ZMod (m ^ (n + 1)) × ZMod (m ^ (n + 1))) ≃ₗ[ZMod (m ^ (n + 1))]
      PowerTorsion m G (n + 1) := by
  classical
  let R := ZMod (m ^ (n + 1))
  let V := PowerTorsion m G (n + 1)
  let P := generator m B h 0 n
  let Q := generator m B h 1 n
  let f := (LinearMap.toSpanSingleton R V P).coprod (LinearMap.toSpanSingleton R V Q)
  letI : NeZero (m ^ (n + 1) : ℕ) := ⟨pow_ne_zero _ hm.ne'⟩
  have hz (a : R × R) (ha : f a = 0) : a = 0 := by
    have hs (r : R) (T : V) : r • T = r.val • T := by
      calc
        _ = (r.val : R) • T :=
          congrArg (fun c : R => c • T) (ZMod.natCast_zmod_val r).symm
        _ = _ := by rw [Nat.cast_smul_eq_nsmul]
    change a.1 • P + a.2 • Q = 0 at ha
    rw [hs a.1 P, hs a.2 Q] at ha
    have hRel : a.1.val • (P : G) + a.2.val • (Q : G) = 0 :=
      congrArg (fun v : V => (v : G)) ha
    obtain ⟨h₀, h₁⟩ := relation_unique m B hm h n a.1.val a.2.val
      (ZMod.val_lt a.1) (ZMod.val_lt a.2) hRel
    exact Prod.ext
      ((ZMod.natCast_zmod_val a.1).symm.trans (by rw [h₀, Nat.cast_zero] <;> rfl))
      ((ZMod.natCast_zmod_val a.2).symm.trans (by rw [h₁, Nat.cast_zero] <;> rfl))
  have hi : Function.Injective f := by
    intro a b hab
    have he : f (a - b) = 0 := by rw [map_sub, hab, sub_self]
    exact sub_eq_zero.mp (hz _ he)
  have hV : Nat.card V = (m * m) ^ (n + 1) := by
    rw [card_powerTorsion m G h (n + 1), first_card m G B]
  letI : Finite V := Nat.finite_of_card_ne_zero (by
    rw [hV]
    exact pow_ne_zero _ (Nat.mul_ne_zero hm.ne' hm.ne'))
  letI : Fintype V := Fintype.ofFinite _
  have hR : Nat.card R = m ^ (n + 1) := by
    change Nat.card (ZMod (m ^ (n + 1))) = _
    rw [Nat.card_zmod]
  have hD : Nat.card (R × R) = (m * m) ^ (n + 1) := by
    rw [Nat.card_prod, hR, ← mul_pow]
  have hc : Fintype.card (R × R) = Fintype.card V := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hD, hV]
  exact LinearEquiv.ofBijective f ((Fintype.bijective_iff_injective_and_card _).mpr ⟨hi, hc⟩)

def levelEquiv : (n : ℕ) →
    (ZMod (m ^ n) × ZMod (m ^ n)) ≃ₗ[ZMod (m ^ n)] PowerTorsion m G n
  | 0 => zeroLevelEquiv m G
  | n + 1 => positiveLevelEquiv m G B hm h n

theorem levelEquiv_succ_apply (n : ℕ)
    (a : ZMod (m ^ (n + 1)) × ZMod (m ^ (n + 1))) :
    levelEquiv m G B hm h (n + 1) a =
      a.1 • generator m B h 0 n + a.2 • generator m B h 1 n := rfl

theorem transition_levelEquiv (n : ℕ)
    (a : ZMod (m ^ (n + 1)) × ZMod (m ^ (n + 1))) :
    transition m G n (levelEquiv m G B hm h (n + 1) a) =
      levelEquiv m G B hm h n
        (PadicResidueSystems.reduction m (Nat.le_succ n) a.1,
          PadicResidueSystems.reduction m (Nat.le_succ n) a.2) := by
  cases n with
  | zero =>
    have hz (P : PowerTorsion m G 0) : (P : G) = 0 := by
      simpa only [pow_zero, one_nsmul] using (mem_iff (m ^ 0) G _).mp P.property
    exact Subtype.ext ((hz _).trans (hz _).symm)
  | succ n =>
    simp only [levelEquiv_succ_apply, map_add, transition_smul m G hm.ne', generator_transition]

end
end ManuscriptAudit.PowerTorsionCompatibleBasis

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.PowerTorsionCompatibleBasis.levelEquiv,
      ``ManuscriptAudit.PowerTorsionCompatibleBasis.levelEquiv_succ_apply,
      ``ManuscriptAudit.PowerTorsionCompatibleBasis.transition_levelEquiv] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
