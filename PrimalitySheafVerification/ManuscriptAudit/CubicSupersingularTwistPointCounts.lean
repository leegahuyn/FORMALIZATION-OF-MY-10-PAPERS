import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicRotationalFixedKernel
import PrimalitySheafVerification.ManuscriptAudit.CubicSexticRotation
import PrimalitySheafVerification.ManuscriptAudit.CubicSupersingularUnitTorsion
import PrimalitySheafVerification.ManuscriptAudit.CubicThreeAdicFrobenius
import PrimalitySheafVerification.ManuscriptAudit.CubicTwistNormArithmetic
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassFiniteFieldFixedCount

/-! Projective point counts from the native geometric twist action. -/

namespace ManuscriptAudit.CubicSupersingularTwistPointCounts

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate CubicCubeRotation
open CubicNonsplitThreeAdicTrace CubicNonsplitFrobeniusTrace CubicThreeFrobeniusSigns
open CubicSupersingularUnitFrobenius CubicSupersingularUnitTorsion CubicRotationQuadratic
open CubicSexticRotation CubicTwistNormArithmetic AdditiveKernelComposition

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (L : Type*) [Field L] [DecidableEq L] [Algebra (ZMod p) L] [IsAlgClosed L]
variable [Algebra.IsAlgebraic (ZMod p) L]
variable (E : Type*) [Field E] [Fintype E] [DecidableEq E] [Algebra E L]

theorem count_from_rotation (hp : 5 ≤ p) (hp₃ : p % 3 = 2)
    (h₂ : (2 : L) ≠ 0) (h₃ : (3 : L) ≠ 0) (hΔ : (shortCubic (0 : L) 1).Δ ≠ 0)
    {A : E} {z : L} (hz : z ^ 3 = 1) (s : ℤ) (hs : (p : ℤ) ∣ s)
    (e : UnitPoints L ≃+ GeometricPoints E L A)
    (he : ∀ P, arithmeticPointFrobenius E L A (e P) = e (s • rotate z hz hΔ P)) :
    (Nat.card (shortCubic (0 : E) A).toProjective.Point : ℤ) =
      if z = 1 then (1 - s) ^ 2 else 1 + s + s * s := by
  let r : AddMonoid.End (UnitPoints L) := rotate z hz hΔ
  let f := arithmeticUnit (ZMod p) L
  let F := arithmeticPointFrobenius E L A
  have hConjCount : Nat.card ↥((1 - F).ker) = Nat.card ↥((1 - s • r).ker) :=
    card_fixed_of_conjugacy e (s • r) F he
  have hCount := (WeierstrassFiniteFieldFixedCount.centered_kernel_card E L A).symm.trans hConjCount
  rw [hCount]
  by_cases h : z = 1
  · have hR : r = 1 := rotate_eq_id L hΔ hz h
    rw [if_pos h, hR]
    exact scalar_kernel_card s (multiplication_and_torsion p L hp hp₃ _
      (scalar_norm_coprime p Fact.out hs)).2
  rw [if_neg h]
  let n := (1 + s + s * s).toNat
  have hPos := rotational_norm_pos s
  have hn : (n : ℤ) = 1 + s + s * s := Int.toNat_of_nonneg (le_of_lt hPos)
  have hn₀ : 0 < n := by omega
  have hCube : r ^ 3 = 1 := by
    apply AddMonoidHom.ext
    intro P
    change r (r (r P)) = P
    exact rotate_cube hz hΔ P
  have hQuad : r ^ 2 + r + 1 = 0 := by
    apply AddMonoidHom.ext
    intro P
    change r (r P) + r P + P = 0
    exact rotate_sum_eq_zero h₂ h₃ one_ne_zero hz h hΔ P
  have hG : FiniteField.frobeniusAlgHom (ZMod p) L z = z ^ 2 := by
    change z ^ Fintype.card (ZMod p) = z ^ 2
    rw [ZMod.card, pow_cube_reduce z _ hz, hp₃]
  have hConj : f * r = r ^ 2 * f := by
    apply AddMonoidHom.ext
    intro P
    change f (r P) = r (r (f P))
    exact pointMapAt_conjugates_rotation (ZMod p) L (Curve (1 : ZMod p))
      (unit_baseChange (ZMod p) L) (FiniteField.frobeniusAlgHom (ZMod p) L) hG hz hΔ P
  have hF : Function.Injective f :=
    CubicThreeAdicFrobenius.pointMapAt_injective (ZMod p) L (Curve (1 : ZMod p)) (Curve (1 : L))
      (unit_baseChange (ZMod p) L) (FiniteField.frobeniusAlgHom (ZMod p) L)
  obtain ⟨hSurj, hCard⟩ := multiplication_and_torsion p L hp hp₃ n
    (rotational_norm_coprime p Fact.out hs)
  rw [CubicRotationalFixedKernel.card_fixed r f s hCube hQuad hConj hF n hn hn₀ hSurj hCard]
  exact hn

end
end ManuscriptAudit.CubicSupersingularTwistPointCounts

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicSupersingularTwistPointCounts.count_from_rotation
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
