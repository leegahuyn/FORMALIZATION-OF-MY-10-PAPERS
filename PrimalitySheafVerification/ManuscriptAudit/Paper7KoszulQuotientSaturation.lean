import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import PrimalitySheafVerification.ManuscriptAudit.Paper7KoszulCRTBaseChange

/-! The literal length-one Koszul complex has a simple exact saturation
criterion after any quotient base change. -/

namespace ManuscriptAudit.Paper7KoszulQuotientSaturation

open CategoryTheory
open Paper7KoszulCRTBaseChange (rankOne)

noncomputable section

variable (R : Type*) [CommRing R]

/-- The native degree-one homology is the actual multiplication kernel. -/
def homologyIsoKernel (a : R) :
    (rankOne R a).homology ≅
      ModuleCat.of R (LinearMap.ker (a • (LinearMap.id : R →ₗ[R] R))) := by
  let K := rankOne R a
  exact (K.isoHomologyπ rfl).symm ≪≫ K.moduleCatCyclesIso

theorem exact_iff_regular (a : R) :
    (rankOne R a).Exact ↔ IsSMulRegular R a := by
  rw [(rankOne R a).exact_iff_mono rfl, ModuleCat.mono_iff_injective] <;> rfl

/-- Exactness of the literal residue boundary is equivalent to saturation
of the quotient ideal under the given parameter. -/
theorem quotient_exact_iff (I : Ideal R) (a : R) :
    (rankOne (R ⧸ I) (Ideal.Quotient.mk I a)).Exact ↔
      ∀ x : R, a * x ∈ I → x ∈ I := by
  rw [exact_iff_regular]
  constructor
  · intro h x hx
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply h
    change Ideal.Quotient.mk I a * Ideal.Quotient.mk I x =
      Ideal.Quotient.mk I a * 0
    rw [mul_zero, ← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
  · intro h x y hxy
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective y
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply h
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change Ideal.Quotient.mk I a * Ideal.Quotient.mk I u =
      Ideal.Quotient.mk I a * Ideal.Quotient.mk I v at hxy
    rw [map_mul, map_sub, mul_sub, hxy, sub_self]

end
end ManuscriptAudit.Paper7KoszulQuotientSaturation

open Lean Elab Command in
run_cmd do
  let names := [``ManuscriptAudit.Paper7KoszulQuotientSaturation.homologyIsoKernel,
    ``ManuscriptAudit.Paper7KoszulQuotientSaturation.quotient_exact_iff]
  for name in names do
    let ax ← collectAxioms name
    let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
