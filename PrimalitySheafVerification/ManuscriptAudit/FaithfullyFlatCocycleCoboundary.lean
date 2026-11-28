import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.FaithfullyFlatCocyclePicard

/-! The triviality test for the invertible module descended from a unit cocycle. -/

namespace ManuscriptAudit.FaithfullyFlatCocyclePicard

open TensorProduct TwistedTensorEqualizer FlatTwistedDescentLine

noncomputable section

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
variable (t : (Double A B)ˣ) (ht : IsCocycle A B t)

/-- The actual affine Picard class of the invertible module descended from t. -/
def picardClass : CommRing.Pic A :=
  letI := invariants_invertible A B t ht
  CommRing.Pic.mk A (invariants A B t)

/-- Trivial Picard class supplies an actual unit coboundary on the cover. -/
theorem exists_coboundary_of_picard_one (h : picardClass A B t ht = 1) :
    ∃ v : Bˣ, t = (Units.map (first A B).toMonoidHom v)⁻¹ *
      Units.map (second A B).toMonoidHom v := by
  let L := invariants A B t
  letI : Module.Invertible A L := invariants_invertible A B t ht
  have he : CommRing.Pic.mk A L = 1 := h
  obtain ⟨e'⟩ := CommRing.Pic.mk_eq_one_iff.mp he
  let e : A ≃ₗ[A] L := e'.symm
  let T : B ≃ₗ[B] B := (AlgebraTensorModule.rid A B B).symm.trans
    ((e.baseChange A B A L).trans (extensionEquiv A B t ht))
  have hEval (b : B) : T b = b * T 1 := by
    have hsmul := T.map_smul b (1 : B)
    simpa only [smul_eq_mul, mul_one] using hsmul
  have hInv : T.symm 1 * T 1 = 1 := by rw [← hEval, T.apply_symm_apply]
  let v : Bˣ := ⟨T 1, T.symm 1, (mul_comm _ _).trans hInv, hInv⟩
  have hv : (v : B) = (e 1).val := by
    change extension A B t ((1 : B) ⊗ₜ[A] e 1) = _
    rw [extension_tmul, one_mul]
  have hx : second A B (v : B) = (t : Double A B) * first A B (v : B) := by
    rw [hv]
    exact (mem_invariants A B t _).1 (e 1).property
  refine ⟨v, Units.ext ?_⟩
  change (t : Double A B) = first A B (↑(v⁻¹) : B) * second A B (v : B)
  rw [hx, mul_left_comm, ← map_mul, Units.inv_mul, map_one, mul_one]

end

end ManuscriptAudit.FaithfullyFlatCocyclePicard

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.FaithfullyFlatCocyclePicard.picardClass,
      ``ManuscriptAudit.FaithfullyFlatCocyclePicard.exists_coboundary_of_picard_one] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
