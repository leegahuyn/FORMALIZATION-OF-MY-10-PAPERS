import Lean.Util.CollectAxioms
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.LinearAlgebra.TensorProduct.Tower
import PrimalitySheafVerification.ManuscriptAudit.Paper7KoszulCRTBaseChange

/-! The degree-one class from the actual rank-one Koszul base change
is identified with the prime field of order five. -/

namespace ManuscriptAudit.Paper7KoszulCRTResidue

open CategoryTheory
open Paper7KoszulCRTBaseChange
open scoped TensorProduct

noncomputable section

private abbrev P : Ideal ℤ := Ideal.span ({(5 : ℤ)} : Set ℤ)

private local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

private theorem P_maximal : P.IsMaximal := by
  let e : ℤ ⧸ P ≃+* ZMod 5 := Int.quotientSpanNatEquivZMod 5
  apply Ideal.Quotient.maximal_of_isField P
  refine ⟨⟨0, 1, ?_⟩, mul_comm, ?_⟩
  · intro h
    exact (zero_ne_one : (0 : ZMod 5) ≠ 1) (by simpa using congrArg e h)
  · intro a ha
    have ha' : e a ≠ 0 := fun h ↦ ha (e.injective (h.trans e.map_zero.symm))
    refine ⟨e.symm ((e a)⁻¹), e.injective ?_⟩
    rw [map_mul, e.apply_symm_apply, mul_inv_cancel₀ ha', map_one]

theorem quotient_ideal_eq_maximal : I = IsLocalRing.maximalIdeal R := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  change Ideal.span ({(5:R)} : Set R) = Ideal.map (algebraMap ℤ R) P
  rw [P, Ideal.map_span, Set.image_singleton, map_ofNat]

/-- The literal quotient of the native five-local integers is the actual
prime field, using its canonical restriction to integral residues. -/
def crtFieldEquiv : S ≃+* ZMod 5 := by
  letI := P_maximal
  exact (Ideal.quotEquivOfEq quotient_ideal_eq_maximal).trans
    ((IsLocalization.AtPrime.equivQuotMaximalIdeal P R).symm.trans
      (Int.quotientSpanNatEquivZMod 5))

/-- The base-changed boundary actually vanishes after tensoring; this
is checked on all finite sums of pure tensors. -/
theorem tensor_boundary_zero :
    ((5:R) • (LinearMap.id : R →ₗ[R] R)).lTensor S = 0 := by
  apply LinearMap.ext
  intro z
  change (((5:R) • (LinearMap.id : R →ₗ[R] R)).lTensor S) z = 0
  induction z with
  | zero => simp
  | tmul a b =>
      let e := AlgebraTensorModule.rid R S S
      apply e.injective
      rw [LinearMap.lTensor_tmul, AlgebraTensorModule.rid_tmul, map_zero]
      change algebraMap R S ((5 : R) * b) * a = 0
      change reduction ((5 : R) * b) * a = 0
      rw [map_mul, reduction_parameter, zero_mul, zero_mul]
  | add a b ha hb => rw [map_add, ha, hb, add_zero]

/-- The actual degree-one homology after CRT is the entire residue module. -/
def after_homology_iso :
    (rankOne S (reduction 5)).homology ≅ ModuleCat.of S S := by
  let K := rankOne S (reduction 5)
  have hG : K.g = 0 := by
    change ModuleCat.ofHom (reduction 5 • (LinearMap.id : S →ₗ[S] S)) = 0
    rw [reduction_parameter, zero_smul] <;> rfl
  exact (ShortComplex.HomologyData.ofZeros K rfl hG).left.homologyIso

end
end ManuscriptAudit.Paper7KoszulCRTResidue

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.Paper7KoszulCRTResidue.crtFieldEquiv,
      ``ManuscriptAudit.Paper7KoszulCRTResidue.tensor_boundary_zero,
      ``ManuscriptAudit.Paper7KoszulCRTResidue.after_homology_iso] do
    let ax ← collectAxioms name
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
