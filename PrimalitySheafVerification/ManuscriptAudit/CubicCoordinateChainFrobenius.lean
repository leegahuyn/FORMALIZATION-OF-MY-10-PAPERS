import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicCoordinateChain
import PrimalitySheafVerification.ManuscriptAudit.CubicPolynomialGuard
import PrimalitySheafVerification.ManuscriptAudit.CubicCofiniteHom
import PrimalitySheafVerification.ManuscriptAudit.CubicFrobeniusScaling

/-! A certified cofinite coordinate chain identifies the actual prime-field Frobenius. -/

namespace ManuscriptAudit.CubicCoordinateChainFrobenius

open Polynomial WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate
open CubicCoordinateChain CubicPolynomialGuard CubicFractionCertificates
open CubicCofiniteHom CubicFrobeniusScaling

noncomputable section

variable {p : ℕ} [Fact p.Prime] {L : Type*} [Field L] [Algebra (ZMod p) L]
  [IsAlgClosed L] [DecidableEq L] {A z : ZMod p}

set_option maxHeartbeats 1300000 in
theorem native_eq_of_chain {dx dy : ℕ} (hpx : p = 3 * dx + 1) (hpy : p = 2 * dy + 1)
    (h₂ : (2 : L) ≠ 0) (hz : (algebraMap (ZMod p) L z) ^ 3 = 1)
    (hΔ : (shortCubic (0 : L) (algebraMap (ZMod p) L A)).Δ ≠ 0)
    {term : Term}
    (chain : Chain A z term (Fraction.polynomial (X ^ dx)) (Fraction.polynomial ((X + C A) ^ dy)))
    (hChain : ∀ f ∈ chain.guards, f ≠ 0) :
    nativeMap (ZMod p) L (FiniteField.frobeniusAlgHom (ZMod p) L) A =
      term.hom (CubicCubeRotation.rotate (algebraMap (ZMod p) L z) hz hΔ) := by
  let P : List ((ZMod p)[X]) := X :: (X + C A) :: chain.guards
  have hNonzero : ∀ f ∈ P, f ≠ 0 := by
    intro f hf
    change f ∈ X :: (X + C A) :: chain.guards at hf
    simp only [List.mem_cons] at hf
    rcases hf with rfl | rfl | hf
    · exact X_ne_zero
    · have hMonic : (X ^ 1 + C A).Monic := monic_X_pow_add_C A (by decide)
      simpa only [pow_one] using hMonic.ne_zero
    · exact hChain f hf
  apply cubicHom_ext hΔ _ _ (exceptional_finite P hNonzero)
  intro x y hP hxBad
  have hGuard (f : (ZMod p)[X]) (hf : f ∈ P) : f.eval₂ (algebraMap (ZMod p) L) (x ^ 3) ≠ 0 :=
    evaluate_ne_zero hxBad hf
  have hx₀ : x ^ 3 ≠ 0 := by simpa only [eval₂_X] using hGuard X (by simp [P])
  have hs : x ^ 3 + algebraMap (ZMod p) L A ≠ 0 := by
    have h := hGuard (X + C A) (by simp [P])
    rw [eval₂_add, eval₂_X, eval₂_C] at h
    exact h
  have hx : x ≠ 0 := fun h => hx₀ (by simp [h])
  have he := (nonsingular_iff hΔ x y).mp hP
  have hy : y ≠ 0 := fun h => hs (by simpa only [h, zero_pow (by decide : (2 : ℕ) ≠ 0)] using he.symm)
  obtain ⟨_, _, hQ, eQ⟩ := chain_coordinates chain h₂ hz hΔ hx hy hP
    (fun f hf => hGuard f (by simp [P, hf]))
  let g := FiniteField.frobeniusAlgHom (ZMod p) L
  have hg (w : L) : g w = w ^ p := by
    change w ^ Fintype.card (ZMod p) = _
    rw [ZMod.card]
  obtain ⟨hF, eF⟩ := nativeMap_some (ZMod p) L g A hP
  have hX : x * (Fraction.polynomial ((X : (ZMod p)[X]) ^ dx)).evaluate (x ^ 3) = x ^ p := by
    simp only [Fraction.evaluate_polynomial, eval₂_pow, eval₂_X]
    rw [hpx, pow_add, pow_mul, pow_one]
    ring
  have hY : y * (Fraction.polynomial (((X : (ZMod p)[X]) + C A) ^ dy)).evaluate (x ^ 3) = y ^ p := by
    simp only [Fraction.evaluate_polynomial, eval₂_pow, eval₂_add, eval₂_X, eval₂_C]
    have hpow : y ^ p = y ^ (2 * dy + 1) := congrArg (fun n : ℕ => y ^ n) hpy
    rw [hpow, pow_add, pow_mul, pow_one, ← he]
    ring
  change nativeMap (ZMod p) L g A (Affine.Point.some x y hP) = _
  have hxy : Affine.Point.some (g x) (g y) hF =
      Affine.Point.some (x * (Fraction.polynomial ((X : (ZMod p)[X]) ^ dx)).evaluate (x ^ 3))
        (y * (Fraction.polynomial (((X : (ZMod p)[X]) + C A) ^ dy)).evaluate (x ^ 3)) hQ := by
    rw [Affine.Point.some.injEq]
    exact ⟨(hg x).trans hX.symm, (hg y).trans hY.symm⟩
  exact eF.trans (hxy.trans eQ.symm)

end
end ManuscriptAudit.CubicCoordinateChainFrobenius

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicCoordinateChainFrobenius.native_eq_of_chain
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
