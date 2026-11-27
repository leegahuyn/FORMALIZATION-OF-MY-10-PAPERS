import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.CubicCubeRotation
import PrimalitySheafVerification.ManuscriptAudit.CubicTwoPowerTorsion
import PrimalitySheafVerification.ManuscriptAudit.TwoPowerTorsionBasis
import PrimalitySheafVerification.ManuscriptAudit.TwoPowerTorsionLift

/-! The actual cube rotation is cyclotomic and cyclic on every two-power torsion level. -/

namespace ManuscriptAudit.CubicRotationCyclicBasis

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate CubicThreeTorsion
open CubicThreeTorsionCard CubicCubeRotation CubicDoublingSurjective CubicTwoPowerTorsion
open TorsionFrobeniusModule TwoPowerTorsionTower TwoPowerTorsionBasis TwoPowerTorsionLift

noncomputable section

private theorem eq_zero_of_two_and_three {G : Type*} [AddCommGroup G] {P : G}
    (h₂ : (2 : ℕ) • P = 0) (h₃ : (3 : ℕ) • P = 0) : P = 0 := by
  simpa only [show (3 : ℕ) = 2 + 1 by decide, add_nsmul, one_nsmul, h₂, zero_add] using h₃

private theorem eq_zero_of_twoPower_and_three {G : Type*} [AddCommGroup G]
    (n : ℕ) (P : G) (hₙ : (2 ^ n : ℕ) • P = 0) (h₃ : (3 : ℕ) • P = 0) : P = 0 := by
  induction n with
  | zero => simpa only [pow_zero, one_nsmul] using hₙ
  | succ n ih =>
    have h₂Q : (2 : ℕ) • ((2 ^ n : ℕ) • P) = 0 := by
      rw [← mul_nsmul, ← pow_succ]
      exact hₙ
    have h₃Q : (3 : ℕ) • ((2 ^ n : ℕ) • P) = 0 := by
      rw [← mul_nsmul', mul_nsmul, h₃, nsmul_zero]
    exact ih (eq_zero_of_two_and_three h₂Q h₃Q)

variable {K : Type*} [Field K] [DecidableEq K] {A z : K}

/-- A fixed point of a nontrivial cube rotation is genuine three-torsion. -/
theorem rotate_fixed_three_torsion (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0)
    (hz : z ^ 3 = 1) (hz₁ : z ≠ 1) (P : (Curve A).Point)
    (hP : rotate z hz (shortCubic_discriminant_ne_zero h₂ h₃ hA) P = P) :
    (3 : ℕ) • P = 0 := by
  let hΔ := shortCubic_discriminant_ne_zero h₂ h₃ hA
  cases P with
  | zero => exact nsmul_zero _
  | some x y hxy =>
    have he := congrArg (abscissa (A := A)) hP
    rw [rotate_abscissa, abscissa_some] at he
    have hmul : (z - 1) * x = 0 := by rw [sub_mul, one_mul, he, sub_self]
    have hx : x = 0 := (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hz₁)
    subst x
    have hy : y ≠ 0 := by
      intro h
      exact hA (by simpa [h] using ((nonsingular_iff hΔ 0 y).mp hxy).symm)
    exact (three_nsmul_affine_some_iff h₂ h₃ hΔ hxy).mpr ⟨hy, zero_mul _⟩

def rotationLinear (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0)
    (hz : z ^ 3 = 1) (n : ℕ) : Module.End (ZMod (2 ^ n)) (PowerTorsion (Curve A).Point n) :=
  mapLinear (2 ^ n) (rotate z hz (shortCubic_discriminant_ne_zero h₂ h₃ hA))

theorem rotation_linear_cube (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0)
    (hz : z ^ 3 = 1) (n : ℕ) (P : PowerTorsion (Curve A).Point n) :
    let R := rotationLinear h₂ h₃ hA hz n
    R (R (R P)) = P :=
  Subtype.ext (rotate_cube hz (shortCubic_discriminant_ne_zero h₂ h₃ hA) (P : (Curve A).Point))

theorem rotation_linear_fixed_zero (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0)
    (hz : z ^ 3 = 1) (hz₁ : z ≠ 1) (n : ℕ) (P : PowerTorsion (Curve A).Point n)
    (hP : rotationLinear h₂ h₃ hA hz n P = P) : P = 0 := by
  apply Subtype.ext
  change (P : (Curve A).Point) = 0
  exact eq_zero_of_twoPower_and_three n (P : (Curve A).Point)
    ((mem_iff (2 ^ n) _ _).mp P.property)
    (rotate_fixed_three_torsion h₂ h₃ hA hz hz₁ _
      (congrArg (fun Q : PowerTorsion (Curve A).Point n => (Q : (Curve A).Point)) hP))

/-- The actual rotation satisfies the quadratic cyclotomic relation on geometric two-power torsion. -/
theorem rotation_linear_quad (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0)
    (hz : z ^ 3 = 1) (hz₁ : z ≠ 1) (n : ℕ) (P : PowerTorsion (Curve A).Point n) :
    let R := rotationLinear h₂ h₃ hA hz n
    R (R P) = -P - R P := by
  let R := rotationLinear h₂ h₃ hA hz n
  change R (R P) = -P - R P
  have hc : R (R (R P)) = P := rotation_linear_cube h₂ h₃ hA hz n P
  have hs : R (R P) + R P + P = 0 := by
    apply rotation_linear_fixed_zero h₂ h₃ hA hz hz₁ n
    change R (R (R P) + R P + P) = _
    rw [map_add, map_add, hc]
    abel
  have he : R (R P) + (R P + P) = 0 := by simpa only [← add_assoc] using hs
  simpa only [neg_add_rev, sub_eq_add_neg] using eq_neg_of_add_eq_zero_left he

variable [IsAlgClosed K]

/-- A basis consisting of one actual lifted point and its actual cube-rotation image. -/
theorem exists_rotation_basis (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0)
    (hz : z ^ 3 = 1) (hz₁ : z ≠ 1) (n : ℕ) :
    ∃ B : Module.Basis (Fin 2) (ZMod (2 ^ (n + 1))) (PowerTorsion (Curve A).Point (n + 1)),
      rotationLinear h₂ h₃ hA hz (n + 1) (B 0) = B 1 := by
  let G := (Curve A).Point
  have hd : Function.Surjective (fun P : G => (2 : ℕ) • P) := affine_doubling_surjective h₂ h₃ hA
  have hf : Nat.card (Torsion 2 G) = 4 :=
    (Nat.card_congr (carrierEquiv 2 _)).trans
      (by simpa only [pow_one] using affine_twoPower_card h₂ h₃ hA 1)
  letI : Finite (Torsion 2 G) := Nat.finite_of_card_ne_zero (by rw [hf]; decide)
  let B₀ := FrobeniusModTwoLinear.basisOfCardFour (Torsion 2 G) hf
  let T : PowerTorsion G 1 := B₀ 0
  have hT : (T : G) ≠ 0 := fun he => B₀.ne_zero 0 (Subtype.ext he)
  let P := lifted G hd T n
  let S := rotationLinear h₂ h₃ hA hz (n + 1)
  let Q := S P
  let r := rotate z hz (shortCubic_discriminant_ne_zero h₂ h₃ hA)
  have hp : (2 ^ n : ℕ) • (P : G) = (T : G) := scale_lifted G hd T n
  have hq : (2 ^ n : ℕ) • (Q : G) = r (T : G) := by
    change (2 ^ n : ℕ) • r (P : G) = _
    rw [← map_nsmul, hp]
  have hrne : r (T : G) ≠ 0 := by
    intro hr
    have hc := rotate_cube hz (shortCubic_discriminant_ne_zero h₂ h₃ hA) (T : G)
    change r (r (r (T : G))) = (T : G) at hc
    rw [hr, map_zero, map_zero] at hc
    exact hT hc.symm
  have hpq : (T : G) ≠ r (T : G) := by
    intro he
    have ht : rotationLinear h₂ h₃ hA hz 1 T = T := Subtype.ext he.symm
    have hzT := rotation_linear_fixed_zero h₂ h₃ hA hz hz₁ 1 T ht
    have ht₀ := congrArg (fun t : PowerTorsion G 1 => (t : G)) hzT
    change (T : G) = 0 at ht₀
    exact hT ht₀
  let e := levelEquivFromLifts G hd hf n P Q (hp.symm ▸ hT) (hq.symm ▸ hrne)
    (by rw [hp, hq]; exact hpq)
  let B := (Module.Basis.finTwoProd (ZMod (2 ^ (n + 1)))).map e
  have he₀ : B 0 = P := by simp [B, e, levelEquivFromLifts_apply]
  have he₁ : B 1 = Q := by simp [B, e, levelEquivFromLifts_apply]
  refine ⟨B, ?_⟩
  change S (B 0) = B 1
  rw [he₀, he₁]

end
end ManuscriptAudit.CubicRotationCyclicBasis

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicRotationCyclicBasis.rotate_fixed_three_torsion,
      ``ManuscriptAudit.CubicRotationCyclicBasis.rotation_linear_fixed_zero,
      ``ManuscriptAudit.CubicRotationCyclicBasis.rotation_linear_quad,
      ``ManuscriptAudit.CubicRotationCyclicBasis.exists_rotation_basis] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
