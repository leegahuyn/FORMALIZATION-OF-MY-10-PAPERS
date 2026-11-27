import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.TorsionFrobeniusModule

/-! The q-power map of a finite extension is the corresponding power of prime-field Frobenius. -/

namespace ManuscriptAudit.FiniteExtensionFrobeniusPower

open WeierstrassCurve WeierstrassFrobeniusExtensionFixed TorsionFrobeniusModule

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (E : Type*) [Field E] [Fintype E] [Algebra (ZMod p) E]
variable (L : Type*) [Field L] [Algebra (ZMod p) L] [Algebra E L]
  [IsScalarTower (ZMod p) E L]

/-- The actual scalar Frobenius on E agrees with the corresponding iterate over the prime field. -/
theorem restrict_frobenius_eq_power :
    (FiniteField.frobeniusAlgHom E L).restrictScalars (ZMod p) =
      (FiniteField.frobeniusAlgHom (ZMod p) L) ^ Module.finrank (ZMod p) E := by
  ext x
  change x ^ Fintype.card E =
    ((FiniteField.frobeniusAlgHom (ZMod p) L) ^ Module.finrank (ZMod p) E) x
  rw [pow_frobenius_apply, Module.card_eq_pow_finrank (K := ZMod p) (V := E), ZMod.card]

/-- The equality of the actual Frobenius operators on a prime-field curve's geometric torsion. -/
theorem actual_torsion_power_eq_extension_map [DecidableEq L] (m : ℕ) (W : Affine (ZMod p)) :
    frobeniusLinear m p L W ^ Module.finrank (ZMod p) E =
      pointMap m W ((FiniteField.frobeniusAlgHom E L).restrictScalars (ZMod p)) := by
  rw [frobeniusLinear_pow_eq_pointMap, restrict_frobenius_eq_power p E L]

end
end ManuscriptAudit.FiniteExtensionFrobeniusPower

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.FiniteExtensionFrobeniusPower.restrict_frobenius_eq_power,
      ``ManuscriptAudit.FiniteExtensionFrobeniusPower.actual_torsion_power_eq_extension_map] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
