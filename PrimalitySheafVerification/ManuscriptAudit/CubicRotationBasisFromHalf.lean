import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicRotationCyclicBasis

/-! A cyclic four-torsion basis containing a specified geometric half. -/

namespace ManuscriptAudit.CubicRotationBasisFromHalf

open Module FiniteFieldPointCount CubicThreeTorsionOrdinate CubicThreeTorsionCard
open CubicCubeRotation CubicRotationCyclicBasis CubicDoublingSurjective CubicTwoPowerTorsion
open TorsionFrobeniusModule TwoPowerTorsionTower TwoPowerTorsionBasis

noncomputable section

variable {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] {A z : K}

/-- The chosen half and its actual cube rotation form a basis when their doubles are
distinct nonzero two-torsion points. -/
theorem exists_basis_from_half (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0)
    (hz : z ^ 3 = 1) (T P : (Curve A).Point) (hT : T ≠ 0) (hT₂ : (2 : ℕ) • T = 0)
    (hDouble : (2 : ℕ) • P = T)
    (hDist : T ≠ rotate z hz (shortCubic_discriminant_ne_zero h₂ h₃ hA) T) :
    ∃ B : Basis (Fin 2) (ZMod 4) (PowerTorsion (Curve A).Point 2),
      (B 0).val = P ∧ rotationLinear h₂ h₃ hA hz 2 (B 0) = B 1 := by
  let G := (Curve A).Point
  let r := rotate z hz (shortCubic_discriminant_ne_zero h₂ h₃ hA)
  let S := rotationLinear h₂ h₃ hA hz 2
  let P₄ : PowerTorsion G 2 := ⟨P, by
    change (4 : ℕ) • P = 0
    rw [show (4 : ℕ) = 2 * 2 by decide, mul_nsmul', hDouble, hT₂]⟩
  let Q₄ := S P₄
  have hp : (2 ^ 1 : ℕ) • P₄.val = T := hDouble
  have hq : (2 ^ 1 : ℕ) • Q₄.val = r T := by
    change (2 : ℕ) • r P = r T
    rw [← map_nsmul, hDouble]
  have hr : r T ≠ 0 := by
    intro h
    have hCube : r (r (r T)) = T :=
      rotate_cube hz (shortCubic_discriminant_ne_zero h₂ h₃ hA) T
    rw [h, map_zero, map_zero] at hCube
    exact hT hCube.symm
  have hd : Function.Surjective (fun x : G => (2 : ℕ) • x) :=
    affine_doubling_surjective h₂ h₃ hA
  have hc : Nat.card (Torsion 2 G) = 4 :=
    (Nat.card_congr (carrierEquiv 2 G)).trans (affine_twoPower_card h₂ h₃ hA 1)
  let e := levelEquivFromLifts G hd hc 1 P₄ Q₄
    (hp.symm ▸ hT) (hq.symm ▸ hr) (by rw [hp, hq]; exact hDist)
  let B := (Basis.finTwoProd (ZMod (2 ^ (1 + 1)))).map e
  have hEval (v : ZMod (2 ^ (1 + 1)) × ZMod (2 ^ (1 + 1))) :
      e v = v.1 • P₄ + v.2 • Q₄ :=
    levelEquivFromLifts_apply G hd hc 1 P₄ Q₄ _ _ _ v
  have h₀ : B 0 = P₄ := by
    have h : e (1, 0) = P₄ := by rw [hEval] <;> simp
    simpa [B] using h
  have h₁ : B 1 = Q₄ := by
    have h : e (0, 1) = Q₄ := by rw [hEval] <;> simp
    simpa [B] using h
  refine ⟨B, ?_, ?_⟩
  · exact congrArg (fun R : PowerTorsion G 2 => R.val) h₀
  · change S (B 0) = B 1
    rw [h₀, h₁]

end
end ManuscriptAudit.CubicRotationBasisFromHalf

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicRotationBasisFromHalf.exists_basis_from_half
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
