import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.PowerTateFiniteKernel
import PrimalitySheafVerification.ManuscriptAudit.CubicSplitPrimeFixedCounts
import PrimalitySheafVerification.ManuscriptAudit.CubicNonsplitTwoThreeAdicCharpoly

/-! Native Frobenius powers minus the identity have nonzero Tate determinant for split primes. -/

namespace ManuscriptAudit.CubicSplitTateFixedDet

open PowerTateModule CubicNonsplitThreeAdicTrace CubicNonsplitTwoThreeAdicCharpoly

noncomputable section

variable (p : ℕ) [Fact p.Prime] (L : Type*) [Field L] [Algebra (ZMod p) L]
  [IsAlgClosed L] [DecidableEq L]

/-- The fixed kernel is finite on geometric points and hence gives an injective
Tate endomorphism with nonzero determinant, uniformly at both coefficient primes. -/
theorem det_pow_sub_one_ne_zero (h₂ : (2 : ZMod p) ≠ 0) (h₃ : (3 : ZMod p) ≠ 0)
    (hs : p % 3 = 1) {A : ZMod p} (hA : A ≠ 0) (n : ℕ) (hn : 0 < n)
    (l : ℕ) [Fact l.Prime] (hl : l = 2 ∨ l = 3) :
    LinearMap.det (endMap l (arithmeticPointFrobenius (ZMod p) L A) ^ n - 1) ≠ 0 := by
  let G := GeometricPoints (ZMod p) L A
  let F := arithmeticPointFrobenius (ZMod p) L A
  have hFinite : Finite ↥((F ^ n - 1).ker) :=
    (CubicSplitPrimeFixedCounts.finite_and_card p L h₂ h₃ hs hA n hn).1
  rcases hl with rfl | rfl
  · simpa only [map_sub, map_pow, map_one] using
      PowerTateFiniteKernel.endMap_det_ne_zero 2 G (F ^ n - 1) hFinite
        (twoAdicBasis (ZMod p) L h₂ h₃ hA)
  · simpa only [map_sub, map_pow, map_one] using
      PowerTateFiniteKernel.endMap_det_ne_zero 3 G (F ^ n - 1) hFinite
        (threeAdicBasis (ZMod p) L h₂ h₃ hA)

end
end ManuscriptAudit.CubicSplitTateFixedDet

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicSplitTateFixedDet.det_pow_sub_one_ne_zero
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
