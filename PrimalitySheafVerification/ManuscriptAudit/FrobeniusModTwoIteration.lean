import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassFrobeniusTwoTorsionTrace

/-! The powers in the native representation are the iterates of Frobenius on points. -/

namespace ManuscriptAudit.FrobeniusModTwoIteration

open WeierstrassCurve TwoTorsionFrobeniusModule
open WeierstrassFrobeniusFixed WeierstrassFrobeniusTwoTorsionTrace

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (L : Type*) [Field L] [Algebra (ZMod p) L]

theorem scalar_iterate_apply (n : ℕ) (x : L) :
    ((⇑(FiniteField.frobeniusAlgHom (ZMod p) L))^[n]) x = x ^ (p ^ n) := by
  simp only [FiniteField.coe_frobeniusAlgHom, ZMod.card]
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, pow_succ, pow_mul]

variable [DecidableEq L] (W : Affine (ZMod p))

/-- The nth linear operator includes into the nth genuine Frobenius iterate on points. -/
theorem point_iterate_inclusion (h : Nat.card (geometricTwoTorsion p L W) = 4)
    (n : ℕ) (P : geometricTwoTorsion p L W) :
    inclusion _ (((frobeniusOfCardFour p L W h).toLinearMap ^ n) P) =
      ((⇑(frobeniusOnPoints p L W))^[n]) (inclusion _ P) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Function.iterate_succ_apply']
    change inclusion _ (frobeniusOfCardFour p L W h
      (((frobeniusOfCardFour p L W h).toLinearMap ^ n) P)) = _
    rw [frobeniusOfCardFour_inclusion, ih]


/-- Over F₂ the arithmetic and inverse Frobenius operators have the same trace. -/
theorem inverse_trace_eq (V : Type*) [AddCommGroup V] [Module (ZMod 2) V]
    (b : Module.Basis (Fin 2) (ZMod 2) V) (F : V ≃ₗ[ZMod 2] V) :
    LinearMap.trace (ZMod 2) V F.symm.toLinearMap = LinearMap.trace (ZMod 2) V F.toLinearMap := by
  apply FrobeniusModTwoLinear.scalar_eq_of_zero_iff
  rw [FrobeniusModTwoLinear.trace_zero_iff_nonzero_fixed V b F.symm,
    FrobeniusModTwoLinear.trace_zero_iff_nonzero_fixed V b F]
  constructor
  · rintro ⟨v, h0, hv⟩
    have h := congrArg (fun x : V => F x) hv
    rw [F.apply_symm_apply] at h
    exact ⟨v, h0, h.symm⟩
  · rintro ⟨v, h0, hv⟩
    have h := congrArg (fun x : V => F.symm x) hv
    rw [F.symm_apply_apply] at h
    exact ⟨v, h0, h.symm⟩

end

end ManuscriptAudit.FrobeniusModTwoIteration

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in
    [``ManuscriptAudit.FrobeniusModTwoIteration.scalar_iterate_apply,
      ``ManuscriptAudit.FrobeniusModTwoIteration.point_iterate_inclusion,
      ``ManuscriptAudit.FrobeniusModTwoIteration.inverse_trace_eq] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter (fun axiomName => !allowed.contains axiomName)
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
