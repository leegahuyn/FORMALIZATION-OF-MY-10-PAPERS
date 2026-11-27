import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper5PrintedAllTwistExtensionCharpoly
import PrimalitySheafVerification.ManuscriptAudit.Paper5GeometricFrobeniusInverse
import PrimalitySheafVerification.ManuscriptAudit.RankTwoInverseTrace
import PrimalitySheafVerification.ManuscriptAudit.FrobeniusDualConvention

/-! Native rational inverse and dual Frobenius coefficients for every printed twist and extension. -/

namespace ManuscriptAudit.Paper5AllTwistInverseExtension

open Module PowerTateModule Paper5PrintedRecurrence
open Paper5PrintedAllTwistTate Paper5PrintedAllTwistExtensionCharpoly
open CubicNonsplitThreeAdicTrace (GeometricPoints)
open Paper5GeometricFrobeniusInverse (determinant_baseChange)
open RankTwoInverseTrace FrobeniusDualConvention
open PrimalitySheafVerification.ManuscriptAudit (paper5TraceCurve)
open scoped TensorProduct

noncomputable section

variable {r : Row} [Fact r.prime.Prime]
variable (L E : Type*) [Field L] [Algebra (ZMod r.prime) L] [IsAlgClosed L] [DecidableEq L]
variable [Algebra.IsAlgebraic (ZMod r.prime) L]
variable [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod r.prime) E]
variable (l : ℕ) [Fact l.Prime]

abbrev RationalTate (A : ZMod r.prime) :=
  ℚ_[l] ⊗[ℤ_[l]] Tate l (GeometricPoints (ZMod r.prime) L A)

theorem inverse_and_dual_coefficients (hr : r ∈ printedRows) (hl : l = 2 ∨ l = 3)
    {A : ZMod r.prime} (hA : A ≠ 0) :
    let t : ℤ := (Fintype.card E : ℤ) + 1 -
      (Nat.card ((paper5TraceCurve r.prime A).baseChange E).toProjective.Point : ℤ)
    let q : ℚ_[l] := Fintype.card E
    ∃ e : RationalTate (r := r) L l A ≃ₗ[ℚ_[l]] RationalTate (r := r) L l A,
      e.toLinearMap = (action r.prime L l A ^ Module.finrank (ZMod r.prime) E).baseChange ℚ_[l] ∧
      LinearMap.trace ℚ_[l] (RationalTate L l A) e.symm.toLinearMap = (t : ℚ_[l]) / q ∧
      LinearMap.det e.symm.toLinearMap = q⁻¹ ∧
      LinearMap.trace ℚ_[l] (Module.Dual ℚ_[l] (RationalTate L l A))
        (dualAction e.symm) = (t : ℚ_[l]) ∧
      LinearMap.det (dualAction e.symm) = q := by
  let t : ℤ := (Fintype.card E : ℤ) + 1 -
    (Nat.card ((paper5TraceCurve r.prime A).baseChange E).toProjective.Point : ℤ)
  let q : ℚ_[l] := Fintype.card E
  let F := (action r.prime L l A ^ Module.finrank (ZMod r.prime) E).baseChange ℚ_[l]
  obtain ⟨B, _, _⟩ := all_printed_twist_coefficients hr L l hl hA
  letI := Module.Free.of_basis B
  letI := Module.Finite.of_basis B
  let b := Algebra.TensorProduct.basis ℚ_[l] B
  letI := Module.Free.of_basis b
  letI := Module.Finite.of_basis b
  have ht : LinearMap.trace ℚ_[l] (RationalTate L l A) F = (t : ℚ_[l]) := by
    have h := all_printed_twist_extension_trace hr L E l hl hA
    dsimp only [F]
    rw [LinearMap.trace_baseChange, h, map_intCast]
  have hd : LinearMap.det F = q := by
    dsimp only [F]
    rw [determinant_baseChange B, all_printed_twist_extension_det L E l hr hl hA, map_natCast]
  have hq : q ≠ 0 := by
    change (Fintype.card E : ℚ_[l]) ≠ 0
    exact_mod_cast (show Fintype.card E ≠ 0 from Fintype.card_pos.ne')
  have hF0 : LinearMap.det F ≠ 0 := hd.symm ▸ hq
  let e := LinearMap.equivOfDetNeZero F hF0
  have he : e.toLinearMap = F := rfl
  have hDual := inverse_generator_coefficients b e
  rw [he, ht, hd] at hDual
  refine ⟨e, he, ?_, ?_, hDual.1, hDual.2⟩
  · apply (eq_div_iff hq).mpr
    have hi := determinant_mul_trace_inverse b e
    rw [he, ht, hd] at hi
    exact (mul_comm _ _).trans hi
  · rw [LinearEquiv.det_coe_symm, he, hd]

end
end ManuscriptAudit.Paper5AllTwistInverseExtension

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper5AllTwistInverseExtension.inverse_and_dual_coefficients
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
