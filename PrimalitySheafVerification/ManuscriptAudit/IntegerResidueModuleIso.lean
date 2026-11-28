import Lean.Util.CollectAxioms
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Data.ZMod.QuotientRing

/-! The actual cyclic integer quotient and the usual residues agree as
integer modules, as well as rings. -/

namespace ManuscriptAudit.IntegerResidueModuleIso

open CategoryTheory

noncomputable section

def quotientResidueIso (n : ℕ) :
    ModuleCat.of ℤ (ℤ ⧸ Ideal.span ({(n : ℤ)} : Set ℤ)) ≅ ModuleCat.of ℤ (ZMod n) := by
  let e := (Int.quotientSpanNatEquivZMod n).toAddEquiv
  let el : (ℤ ⧸ Ideal.span ({(n : ℤ)} : Set ℤ)) ≃ₗ[ℤ] ZMod n :=
    e.toIntLinearEquiv
  exact el.toModuleIso

end
end ManuscriptAudit.IntegerResidueModuleIso

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.IntegerResidueModuleIso.quotientResidueIso
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{name} depends on unexpected axioms {ax}"
  logInfo m!"{name} uses {ax}"
