import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.CubicThreeAdicFrobenius
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryNineteenFrobenius

/-! The native nineteen-torsion of the ordinary centered cubic is the conjugate Frobenius kernel. -/

namespace ManuscriptAudit.Paper5OrdinaryNineteenTorsionKernel

open WeierstrassCurve CubicThreeTorsionOrdinate Paper5OrdinaryNineteenAlgebra
open Paper5OrdinaryNineteenCoordinates Paper5OrdinaryNineteenFrobenius

noncomputable section

local instance : Fact (Nat.Prime 19) := ⟨by decide⟩

variable (L : Type*) [Field L] [Algebra (ZMod 19) L] [CharP L 19] [IsAlgClosed L] [DecidableEq L]

theorem frobenius_injective : Function.Injective (nativeFrobenius L) :=
  CubicThreeAdicFrobenius.pointMapAt_injective (ZMod 19) L
    (Curve (1 : ZMod 19)) (Curve (1 : L)) (ordinary_baseChange L)
    (FiniteField.frobeniusAlgHom (ZMod 19) L)

/-- The actual conjugate in the native rotation ring. -/
def conjugateFrobenius : AddMonoid.End (Points L) :=
  (3 : ℕ) • (1 : AddMonoid.End (Points L)) - (2 : ℕ) • rotation L

theorem frobenius_mul_conjugate_apply (P : Points L) :
    nativeFrobenius L (conjugateFrobenius L P) = (19 : ℕ) • P := by
  have hF (Q : Points L) : nativeFrobenius L Q = (5 : ℕ) • Q + (2 : ℕ) • rotation L Q :=
    congrArg (fun f : AddMonoid.End (Points L) => f Q) (native_eq_rotation L)
  have hV : conjugateFrobenius L P = (3 : ℕ) • P - (2 : ℕ) • rotation L P := rfl
  rw [hF, hV]
  simp only [map_sub, map_nsmul, rotation_sq]
  abel

/-- The nineteen-torsion condition is the native equality [3]P=[2]ρP. -/
theorem torsion_iff (P : Points L) :
    (19 : ℕ) • P = 0 ↔ (3 : ℕ) • P = (2 : ℕ) • rotation L P := by
  constructor
  · intro hp
    have h : nativeFrobenius L (conjugateFrobenius L P) = nativeFrobenius L 0 := by
      rw [frobenius_mul_conjugate_apply, hp, map_zero]
    exact sub_eq_zero.mp (frobenius_injective L h)
  · intro hp
    have h : conjugateFrobenius L P = 0 := sub_eq_zero.mpr hp
    rw [← frobenius_mul_conjugate_apply, h, map_zero]

end
end ManuscriptAudit.Paper5OrdinaryNineteenTorsionKernel

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5OrdinaryNineteenTorsionKernel.frobenius_injective,
      ``ManuscriptAudit.Paper5OrdinaryNineteenTorsionKernel.frobenius_mul_conjugate_apply,
      ``ManuscriptAudit.Paper5OrdinaryNineteenTorsionKernel.torsion_iff] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
