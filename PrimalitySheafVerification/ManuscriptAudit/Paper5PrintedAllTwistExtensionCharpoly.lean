import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper5PrintedAllTwistTate

/-! The full native 2-adic and 3-adic Frobenius polynomial in every extension of every printed twist. -/

namespace ManuscriptAudit.Paper5PrintedAllTwistExtensionCharpoly

open Polynomial Module PowerTateModule
open Paper5PrintedRecurrence Paper5PrintedAllTwistTate CubicNonsplitTwoThreeAdicCharpoly
open PrimalitySheafVerification.ManuscriptAudit (paper5TraceCurve)

noncomputable section

variable {r : Row} [Fact r.prime.Prime]
variable (L E : Type*) [Field L] [Algebra (ZMod r.prime) L] [IsAlgClosed L] [DecidableEq L]
variable [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod r.prime) E]
variable (l : ℕ) [Fact l.Prime]

theorem all_printed_twist_extension_det (hr : r ∈ printedRows) (hl : l = 2 ∨ l = 3)
    {A : ZMod r.prime} (hA : A ≠ 0) :
    LinearMap.det (action r.prime L l A ^ Module.finrank (ZMod r.prime) E) =
      (Fintype.card E : ℤ_[l]) := by
  obtain ⟨B, _, hBase⟩ := all_printed_twist_coefficients hr L l hl hA
  letI := Module.Free.of_basis B
  letI := Module.Finite.of_basis B
  rw [map_pow, hBase, Module.card_eq_pow_finrank (K := ZMod r.prime) (V := E),
    ZMod.card, Nat.cast_pow]

variable [Algebra.IsAlgebraic (ZMod r.prime) L]

theorem all_printed_twist_extension_charpoly (hr : r ∈ printedRows) (hl : l = 2 ∨ l = 3)
    {A : ZMod r.prime} (hA : A ≠ 0) :
    ∃ B : Basis (Fin 2) ℤ_[l] (Tate l (GeometricPoints (ZMod r.prime) L A)),
      letI := Module.Free.of_basis B
      letI := Module.Finite.of_basis B
      (action r.prime L l A ^ Module.finrank (ZMod r.prime) E).charpoly =
        X ^ 2 -
          C (((Fintype.card E : ℤ) + 1 -
            (Nat.card ((paper5TraceCurve r.prime A).baseChange E).toProjective.Point : ℤ) : ℤ) :
              ℤ_[l]) * X + C (Fintype.card E : ℤ_[l]) := by
  obtain ⟨B, _, _⟩ := all_printed_twist_coefficients hr L l hl hA
  refine ⟨B, ?_⟩
  letI := Module.Free.of_basis B
  letI := Module.Finite.of_basis B
  let f := action r.prime L l A ^ Module.finrank (ZMod r.prime) E
  change f.charpoly = _
  have ht := all_printed_twist_extension_trace hr L E l hl hA
  have hd := all_printed_twist_extension_det L E l hr hl hA
  rw [← LinearMap.charpoly_toMatrix f B, Matrix.charpoly_fin_two,
    ← LinearMap.trace_eq_matrix_trace ℤ_[l] B, LinearMap.det_toMatrix B, ht, hd]

end
end ManuscriptAudit.Paper5PrintedAllTwistExtensionCharpoly

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5PrintedAllTwistExtensionCharpoly.all_printed_twist_extension_det,
      ``ManuscriptAudit.Paper5PrintedAllTwistExtensionCharpoly.all_printed_twist_extension_charpoly] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
