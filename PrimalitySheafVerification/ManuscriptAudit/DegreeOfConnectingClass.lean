import Lean.Util.CollectAxioms
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! A divisor degree descends through an actual surjective connecting map
as soon as its kernel consists of degree-zero divisors. -/

namespace ManuscriptAudit.DegreeOfConnectingClass

noncomputable section

variable {D H : Type*} [AddCommGroup D] [AddCommGroup H]
variable (c : D →+ H) (hc : Function.Surjective c)
variable (d : D →+ ℤ) (hk : c.ker ≤ d.ker)

private abbrev e := QuotientAddGroup.quotientKerEquivOfSurjective c hc

/-- Degree on the actual connecting cohomology group. -/
def descendedDegree : H →+ ℤ :=
  (QuotientAddGroup.lift c.ker d hk).comp (e c hc).symm.toAddMonoidHom

theorem descendedDegree_connecting (z : D) :
    descendedDegree c hc d hk (c z) = d z := by
  have hz : c z = e c hc (QuotientAddGroup.mk z) := rfl
  change QuotientAddGroup.lift c.ker d hk ((e c hc).symm (c z)) = d z
  rw [hz, AddEquiv.symm_apply_apply]
  rfl

/-- A single genuine divisor of degree one above the generator proves
that the degree is a retraction of the entire integer Cartier map. -/
theorem descendedDegree_leftInverse (b : ℤ →+ H) (z : D)
    (hb : c z = b 1) (hd : d z = 1) :
    Function.LeftInverse (descendedDegree c hc d hk) b := by
  intro n
  let r := (descendedDegree c hc d hk).comp b
  have h1 : r 1 = 1 := by
    change descendedDegree c hc d hk (b 1) = 1
    rw [← hb, descendedDegree_connecting, hd]
  change r n = n
  calc
    r n = r (n • (1 : ℤ)) := by rw [zsmul_eq_mul, mul_one]
    _ = n • r 1 := map_zsmul r n 1
    _ = n := by rw [h1, zsmul_eq_mul, mul_one]

end

end ManuscriptAudit.DegreeOfConnectingClass

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.DegreeOfConnectingClass.descendedDegree_leftInverse
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
