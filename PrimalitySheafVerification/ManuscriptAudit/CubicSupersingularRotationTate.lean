import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicNonsplitFiniteFieldTate
import PrimalitySheafVerification.ManuscriptAudit.CubicRotationScalarSquare
import PrimalitySheafVerification.ManuscriptAudit.CubicSupersingularUnitFrobenius

/-! The nontrivial cubic rotation has trace -1 and determinant 1 at every admissible prime. -/

namespace ManuscriptAudit.CubicSupersingularRotationTate

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate
open CubicCubeRotation CubicRotationQuadratic CubicThreeFrobeniusSigns
open CubicNonsplitFrobeniusTrace CubicSupersingularUnitFrobenius PowerTateModule

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (L : Type*) [Field L] [Algebra (ZMod p) L] [IsAlgClosed L] [DecidableEq L]
variable [Algebra.IsAlgebraic (ZMod p) L]
variable (l : ℕ) [Fact l.Prime]

theorem trace_det (hp : 5 ≤ p) (hp₃ : p % 3 = 2) (hlp : l ≠ p)
    (h₂ : (2 : L) ≠ 0) (h₃ : (3 : L) ≠ 0)
    (hΔ : (shortCubic (0 : L) 1).Δ ≠ 0) {z : L} (hz : z ^ 3 = 1) (hz₁ : z ≠ 1) :
    let S := endMap l (rotate z hz hΔ)
    LinearMap.trace ℤ_[l] (Tate l (UnitPoints L)) S = -1 ∧ LinearMap.det S = 1 := by
  let B := CubicNonsplitFiniteFieldTate.centeredBasis p L l hp hp₃ hlp one_ne_zero hΔ
  let f := arithmeticUnit (ZMod p) L
  let r : AddMonoid.End (UnitPoints L) := rotate z hz hΔ
  have hSq : f ^ 2 = Int.cast (-(p : ℤ)) := by
    apply AddMonoidHom.ext
    intro P
    rw [pow_two, Int.cast_neg, Int.cast_natCast]
    change f (f P) = -(p • P)
    exact prime_square L p hp hp₃ P
  have hQuad : r ^ 2 + r + 1 = 0 := by
    apply AddMonoidHom.ext
    intro P
    change r (r P) + r P + P = 0
    exact rotate_sum_eq_zero h₂ h₃ one_ne_zero hz hz₁ hΔ P
  have hg : FiniteField.frobeniusAlgHom (ZMod p) L z = z ^ 2 := by
    change z ^ Fintype.card (ZMod p) = z ^ 2
    rw [ZMod.card, pow_cube_reduce z _ hz, hp₃]
  have hConj : f * r = r ^ 2 * f := by
    apply AddMonoidHom.ext
    intro P
    change f (r P) = r (r (f P))
    exact pointMapAt_conjugates_rotation (ZMod p) L (Curve (1 : ZMod p))
      (unit_baseChange (ZMod p) L) (FiniteField.frobeniusAlgHom (ZMod p) L) hg hz hΔ P
  let F := endMap l f
  let S := endMap l r
  let c : ℤ_[l] := -(p : ℤ_[l])
  have hc : c ≠ 0 := neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega))
  have hF : F ^ 2 = c • (1 : Module.End ℤ_[l] (Tate l (UnitPoints L))) := by
    have h := congrArg (endMap l) hSq
    rw [map_pow, map_intCast] at h
    have hCast : (algebraMap ℤ_[l] (Module.End ℤ_[l] (Tate l (UnitPoints L))))
        (Int.cast (-(p : ℤ))) = Int.cast (-(p : ℤ)) := by
      rw [map_intCast]
    simpa only [F, c, Int.cast_neg, Int.cast_natCast, Algebra.algebraMap_eq_smul_one] using
      h.trans hCast.symm
  have hS : S ^ 2 + S + 1 = 0 := by
    simpa only [S, map_add, map_pow, map_one, map_zero] using congrArg (endMap l) hQuad
  have hFS : F * S = S ^ 2 * F := by
    simpa only [F, S, map_mul, map_pow] using congrArg (endMap l) hConj
  exact CubicRotationScalarSquare.trace_det B F S hc hF hS hFS

end
end ManuscriptAudit.CubicSupersingularRotationTate

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicSupersingularRotationTate.trace_det
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
