import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.TwoPowerTorsionTower

/-! The genuine doubling transition is semilinear for reduction of the scalar ring. -/

namespace ManuscriptAudit.TwoPowerTorsionReduction

open TwoPowerTorsionTower

noncomputable section

/-- The native scalar reduction from the (n+1)st ring to the nth. -/
def reduction (n : ℕ) : ZMod (2 ^ (n + 1)) →+* ZMod (2 ^ n) :=
  ZMod.castHom (by rw [pow_succ]; exact dvd_mul_right (2 ^ n) 2) (ZMod (2 ^ n))

variable {G : Type*} [AddCommGroup G]

/-- The actual doubling map respects reduction of coefficients between levels. -/
theorem transition_smul (n : ℕ) (r : ZMod (2 ^ (n + 1))) (P : PowerTorsion G (n + 1)) :
    transition G n (r • P) = reduction n r • transition G n P := by
  letI : NeZero (2 ^ (n + 1) : ℕ) := ⟨pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0)⟩
  have hs : r • P = r.val • P := by
    calc
      _ = (r.val : ZMod (2 ^ (n + 1))) • P :=
        congrArg (fun s : ZMod (2 ^ (n + 1)) => s • P) (ZMod.natCast_zmod_val r).symm
      _ = _ := by rw [Nat.cast_smul_eq_nsmul]
  have hr : reduction n r = (r.val : ZMod (2 ^ n)) := by
    calc
      _ = reduction n (r.val : ZMod (2 ^ (n + 1))) :=
        congrArg (reduction n) (ZMod.natCast_zmod_val r).symm
      _ = _ := map_natCast (reduction n) _
  rw [hs, hr, Nat.cast_smul_eq_nsmul, map_nsmul]

end
end ManuscriptAudit.TwoPowerTorsionReduction

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.TwoPowerTorsionReduction.transition_smul
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
