import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.FrobeniusModTwoLinear
import PrimalitySheafVerification.ManuscriptAudit.TwoPowerTorsionIndependent
import PrimalitySheafVerification.ManuscriptAudit.TwoPowerTorsionTower

/-! Actual free rank two on every positive level of the geometric two-power torsion tower. -/

namespace ManuscriptAudit.TwoPowerTorsionBasis

open TorsionFrobeniusModule TwoPowerTorsionIndependent TwoPowerTorsionTower

noncomputable section

private def pairLinear (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] (P Q : V) :
    (R × R) →ₗ[R] V where
  toFun a := a.1 • P + a.2 • Q
  map_add' a b := by
    change (a.1 + b.1) • P + (a.2 + b.2) • Q = (a.1 • P + a.2 • Q) + (b.1 • P + b.2 • Q)
    rw [add_smul, add_smul]
    abel
  map_smul' a b := by
    change (a * b.1) • P + (a * b.2) • Q = a • (b.1 • P + b.2 • Q)
    rw [mul_smul, mul_smul, smul_add]

variable (G : Type*) [AddCommGroup G]

private theorem power_smul_surjective
    (h : Function.Surjective (fun P : G => (2 : ℕ) • P)) (n : ℕ) :
    Function.Surjective (fun P : G => (2 ^ n : ℕ) • P) := by
  induction n with
  | zero =>
    intro Q
    exact ⟨Q, by rw [pow_zero, one_nsmul]⟩
  | succ n ih =>
    intro Q
    obtain ⟨T, hT⟩ := h Q
    obtain ⟨P, hP⟩ := ih T
    change (2 : ℕ) • T = Q at hT
    change (2 ^ n : ℕ) • P = T at hP
    refine ⟨P, ?_⟩
    change (2 ^ (n + 1) : ℕ) • P = Q
    rw [pow_succ, mul_nsmul, hP, hT]

/-- The zeroth level is the zero module over ZMod 1. -/
def zeroLevelEquiv : (ZMod (2 ^ 0) × ZMod (2 ^ 0)) ≃ₗ[ZMod (2 ^ 0)] PowerTorsion G 0 := by
  letI : Subsingleton (ZMod (2 ^ 0) × ZMod (2 ^ 0)) :=
    inferInstanceAs (Subsingleton (ZMod 1 × ZMod 1))
  have hz (P : PowerTorsion G 0) : (P : G) = 0 := by
    simpa only [pow_zero, one_nsmul] using (mem_iff (2 ^ 0) G _).mp P.property
  letI : Subsingleton (PowerTorsion G 0) := ⟨fun P Q => Subtype.ext ((hz P).trans (hz Q).symm)⟩
  exact LinearEquiv.ofBijective 0 ⟨fun P Q _ => Subsingleton.elim P Q,
    fun Q => ⟨0, Subsingleton.elim _ Q⟩⟩

private def positiveLevelEquiv
    (h : Function.Surjective (fun P : G => (2 : ℕ) • P))
    (hfour : Nat.card (Torsion 2 G) = 4) (n : ℕ) :
    (ZMod (2 ^ (n + 1)) × ZMod (2 ^ (n + 1))) ≃ₗ[ZMod (2 ^ (n + 1))]
      PowerTorsion G (n + 1) := by
  classical
  letI : Finite (Torsion 2 G) := Nat.finite_of_card_ne_zero (by rw [hfour]; decide)
  let B := FrobeniusModTwoLinear.basisOfCardFour (Torsion 2 G) hfour
  let T := B (0 : Fin 2)
  let U := B (1 : Fin 2)
  have hT₀ : (T : G) ≠ 0 := fun he => B.ne_zero 0 (Subtype.ext he)
  have hU₀ : (U : G) ≠ 0 := fun he => B.ne_zero 1 (Subtype.ext he)
  have hTU : (T : G) ≠ (U : G) := fun he =>
    (by decide : (0 : Fin 2) ≠ 1) (B.injective (Subtype.ext he))
  obtain ⟨x, hx⟩ := power_smul_surjective G h n (T : G)
  obtain ⟨y, hy⟩ := power_smul_surjective G h n (U : G)
  change (2 ^ n : ℕ) • x = (T : G) at hx
  change (2 ^ n : ℕ) • y = (U : G) at hy
  have hx₀ : (2 ^ (n + 1) : ℕ) • x = 0 := by
    rw [pow_succ, mul_nsmul, hx]
    exact (mem_iff 2 G _).mp T.property
  have hy₀ : (2 ^ (n + 1) : ℕ) • y = 0 := by
    rw [pow_succ, mul_nsmul, hy]
    exact (mem_iff 2 G _).mp U.property
  let R := ZMod (2 ^ (n + 1))
  let V := PowerTorsion G (n + 1)
  let P : V := ⟨x, (mem_iff (2 ^ (n + 1)) G _).mpr hx₀⟩
  let Q : V := ⟨y, (mem_iff (2 ^ (n + 1)) G _).mpr hy₀⟩
  let F := pairLinear R V P Q
  letI : NeZero (2 ^ (n + 1) : ℕ) := ⟨pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0)⟩
  have hzero (a : R × R) (ha : F a = 0) : a = 0 := by
    have h₁ : a.1 • P = a.1.val • P := by
      calc
        _ = (a.1.val : R) • P :=
          congrArg (fun c : R => c • P) (ZMod.natCast_zmod_val a.1).symm
        _ = _ := by rw [Nat.cast_smul_eq_nsmul]
    have h₂ : a.2 • Q = a.2.val • Q := by
      calc
        _ = (a.2.val : R) • Q :=
          congrArg (fun c : R => c • Q) (ZMod.natCast_zmod_val a.2).symm
        _ = _ := by rw [Nat.cast_smul_eq_nsmul]
    change a.1 • P + a.2 • Q = 0 at ha
    rw [h₁, h₂] at ha
    have har : a.1.val • x + a.2.val • y = 0 :=
      congrArg (fun g : V => (g : G)) ha
    obtain ⟨h₁z, h₂z⟩ :=
      nsmul_relation_unique n x y hx₀ hy₀ (by rw [hx]; exact hT₀) (by rw [hy]; exact hU₀)
        (by rw [hx, hy]; exact hTU) a.1.val a.2.val
        (ZMod.val_lt a.1) (ZMod.val_lt a.2) har
    refine Prod.ext ?_ ?_
    · change a.1 = 0
      rw [← ZMod.natCast_zmod_val a.1, h₁z, Nat.cast_zero]
    · change a.2 = 0
      rw [← ZMod.natCast_zmod_val a.2, h₂z, Nat.cast_zero]
  have hInjective : Function.Injective F := by
    intro a b hab
    have he : F (a - b) = 0 := by rw [map_sub, hab, sub_self]
    exact sub_eq_zero.mp (hzero _ he)
  have hV : Nat.card V = 4 ^ (n + 1) := card_powerTorsion G h hfour (n + 1)
  letI : Finite V := Nat.finite_of_card_ne_zero (by
    rw [hV]
    exact pow_ne_zero _ (by decide : (4 : ℕ) ≠ 0))
  letI : Fintype V := Fintype.ofFinite _
  have hR : Nat.card R = 2 ^ (n + 1) := by
    change Nat.card (ZMod (2 ^ (n + 1))) = _
    rw [Nat.card_eq_fintype_card, ZMod.card]
  have hSource : Nat.card (R × R) = 4 ^ (n + 1) := by
    rw [Nat.card_prod, hR, ← mul_pow]
  have hCard : Fintype.card (R × R) = Fintype.card V := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hSource, hV]
  exact LinearEquiv.ofBijective F ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨hInjective, hCard⟩)

/-- Every native level is isomorphic to a pair of copies of the scalar ring. -/
def levelEquiv (h : Function.Surjective (fun P : G => (2 : ℕ) • P))
    (hfour : Nat.card (Torsion 2 G) = 4) (n : ℕ) :
    (ZMod (2 ^ n) × ZMod (2 ^ n)) ≃ₗ[ZMod (2 ^ n)] PowerTorsion G n :=
  match n with
  | 0 => zeroLevelEquiv G
  | n + 1 => positiveLevelEquiv G h hfour n

/-- The native level, with its actual torsion scalar action, has a two-vector basis. -/
def levelBasis (h : Function.Surjective (fun P : G => (2 : ℕ) • P))
    (hfour : Nat.card (Torsion 2 G) = 4) (n : ℕ) :
    Module.Basis (Fin 2) (ZMod (2 ^ n)) (PowerTorsion G n) :=
  Module.Basis.ofEquivFun
    ((levelEquiv G h hfour n).symm.trans
      ((LinearEquiv.finTwoArrow (ZMod (2 ^ n)) (ZMod (2 ^ n))).symm))

end
end ManuscriptAudit.TwoPowerTorsionBasis

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.TwoPowerTorsionBasis.zeroLevelEquiv,
      ``ManuscriptAudit.TwoPowerTorsionBasis.levelEquiv,
      ``ManuscriptAudit.TwoPowerTorsionBasis.levelBasis] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
