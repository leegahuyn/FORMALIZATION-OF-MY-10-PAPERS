import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicSplitTateFixedDet
import PrimalitySheafVerification.ManuscriptAudit.PowerTateGeometricKernelValuation
import PrimalitySheafVerification.ManuscriptAudit.FirstPrimeTorsionBasis

/-! The prime-adic determinant of the actual Frobenius difference has the exact point-count valuation. -/

namespace ManuscriptAudit.CubicSplitTateFixedValuation

open PowerTateModule CubicNonsplitThreeAdicTrace
open CubicSplitExtensionTraceRecurrence Paper5PrintedRecurrence

noncomputable section

variable (p : ℕ) [Fact p.Prime] (L : Type*) [Field L] [Algebra (ZMod p) L]
  [IsAlgClosed L] [DecidableEq L]

/-- For every positive extension degree, the full Tate determinant difference and
the actual projective count have the same 2-adic and 3-adic valuations. -/
theorem valuation_det_pow_sub_one (h₂ : (2 : ZMod p) ≠ 0) (h₃ : (3 : ZMod p) ≠ 0)
    (hs : p % 3 = 1) {A : ZMod p} (hA : A ≠ 0) (n : ℕ) (hn : 0 < n)
    (l : ℕ) [Fact l.Prime] (hl : l = 2 ∨ l = 3) :
    (LinearMap.det (endMap l (arithmeticPointFrobenius (ZMod p) L A) ^ n - 1)).valuation =
      padicValNat l (((p ^ n : ℕ) : ℤ) + 1 - recurrence p (signedTrace A) n).toNat := by
  let G := GeometricPoints (ZMod p) L A
  let F := arithmeticPointFrobenius (ZMod p) L A
  obtain ⟨hFinite, hCard⟩ := CubicSplitPrimeFixedCounts.finite_and_card p L h₂ h₃ hs hA n hn
  have hC : Nat.card ↥((F ^ n - 1).ker) =
      (((p ^ n : ℕ) : ℤ) + 1 - recurrence p (signedTrace A) n).toNat := by
    simpa using congrArg Int.toNat hCard
  rw [← hC]
  have h₂L : (2 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap (ZMod p) L)).mpr h₂
  have h₃L : (3 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap (ZMod p) L)).mpr h₃
  have hAL : algebraMap (ZMod p) L A ≠ 0 := (map_ne_zero (algebraMap (ZMod p) L)).mpr hA
  rcases hl with rfl | rfl
  · simpa only [map_sub, map_pow, map_one] using
      PowerTateGeometricKernelValuation.valuation_eq_card_kernel 2 G
        (CubicTwoPowerTorsionBasis.affineBasis h₂L h₃L hAL 1)
        (CubicDoublingSurjective.affine_doubling_surjective h₂L h₃L hAL) (F ^ n - 1) hFinite
  · let B := FirstPrimeTorsionBasis.basis 3 G (by
        change Nat.card (PowerTorsionTower.PowerTorsion 3 G 1) = 9
         exact CubicThreeAdicTate.affine_threePower_card h₂L h₃L hAL 1)
    simpa only [map_sub, map_pow, map_one] using
      PowerTateGeometricKernelValuation.valuation_eq_card_kernel 3 G B
        (CubicTriplingSurjective.affine_tripling_surjective h₂L h₃L hAL) (F ^ n - 1) hFinite

end
end ManuscriptAudit.CubicSplitTateFixedValuation

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicSplitTateFixedValuation.valuation_det_pow_sub_one
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
