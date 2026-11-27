import Lean.Util.CollectAxioms
import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! The multiplicative group of the literal affine Weierstrass coordinate ring. -/

namespace ManuscriptAudit.WeierstrassAffineUnits

open Polynomial WeierstrassCurve.Affine

noncomputable section

variable {K : Type*} [Field K] (W : WeierstrassCurve.Affine K)

private theorem scalar_of_unit (u : W.CoordinateRingˣ) :
    ∃ a : Kˣ, algebraMap K W.CoordinateRing (a : K) = (u : W.CoordinateRing) := by
  obtain ⟨p, q, h⟩ := CoordinateRing.exists_smul_basis_eq (u : W.CoordinateRing)
  have hNu : IsUnit (Algebra.norm K[X] (u : W.CoordinateRing)) :=
    u.isUnit.map (Algebra.norm K[X])
  have hDegree : (Algebra.norm K[X] (u : W.CoordinateRing)).degree = 0 :=
    Polynomial.degree_eq_zero_of_isUnit hNu
  have hMax : max (2 • p.degree) (2 • q.degree + 3) = 0 := by
    rw [← CoordinateRing.degree_norm_smul_basis (W' := W) p q, h, hDegree]
  have hq : q = 0 := by
    by_contra hqn
    have hd : 0 ≤ q.degree := Polynomial.zero_le_degree_iff.mpr hqn
    have hd₂ : (0 : WithBot ℕ) ≤ 2 • q.degree := by
      simpa only [two_nsmul] using add_nonneg hd hd
    have hLo : (3 : WithBot ℕ) ≤ 2 • q.degree + 3 := by
      simpa only [zero_add] using add_le_add_right hd₂ (3 : WithBot ℕ)
    have hHi : 2 • q.degree + 3 ≤ (0 : WithBot ℕ) := by
      rw [← hMax]
      exact le_max_right _ _
    exact (by decide : ¬ (3 : WithBot ℕ) ≤ 0) (hLo.trans hHi)
  have hNorm : Algebra.norm K[X] (u : W.CoordinateRing) = p ^ 2 := by
    rw [← h, CoordinateRing.norm_smul_basis, hq]
    simp
  have hPow : IsUnit (p ^ 2) := hNorm ▸ hNu
  have hDiv : p ∣ p ^ 2 := by rw [pow_two]; exact dvd_mul_right p p
  have hp : IsUnit p := isUnit_iff_dvd_one.mpr (hDiv.trans (hPow.dvd : p ^ 2 ∣ 1))
  obtain ⟨a, ha, hConst⟩ := Polynomial.isUnit_iff.mp hp
  obtain ⟨v, hv⟩ := ha
  refine ⟨v, ?_⟩
  rw [← h, hq, zero_smul, add_zero, ← hConst, ← hv, Algebra.smul_def, mul_one]
  exact IsScalarTower.algebraMap_apply K K[X] W.CoordinateRing (v : K)

/-- Constants give all units of the affine coordinate ring of any Weierstrass equation over a field. -/
def unitsEquiv : Kˣ ≃* W.CoordinateRingˣ := by
  refine MulEquiv.ofBijective (Units.map (algebraMap K W.CoordinateRing)) ⟨?_, ?_⟩
  · intro a b h
    apply Units.ext
    apply (algebraMap K W.CoordinateRing).injective
    exact congrArg (fun u : W.CoordinateRingˣ => (u : W.CoordinateRing)) h
  · intro u
    obtain ⟨a, ha⟩ := scalar_of_unit W u
    exact ⟨a, Units.ext ha⟩

theorem unitsEquiv_apply_val (a : Kˣ) :
    (unitsEquiv W a : W.CoordinateRing) = algebraMap K W.CoordinateRing (a : K) := rfl

/-- Over the algebraic closure the Kummer power map on genuine affine coordinate units is onto. -/
theorem unit_power_surjective [IsAlgClosed K] (d : ℕ) (hd : 0 < d) :
    Function.Surjective (fun u : W.CoordinateRingˣ => u ^ d) := by
  intro u
  obtain ⟨a, rfl⟩ := (unitsEquiv W).surjective u
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (a : K) hd
  have hbn : b ≠ 0 := by
    intro h
    rw [h, zero_pow hd.ne'] at hb
    exact a.ne_zero hb.symm
  refine ⟨unitsEquiv W (Units.mk0 b hbn), ?_⟩
  change (unitsEquiv W (Units.mk0 b hbn)) ^ d = unitsEquiv W a
  rw [← map_pow]
  apply congrArg (unitsEquiv W)
  exact Units.ext hb

end
end ManuscriptAudit.WeierstrassAffineUnits

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.WeierstrassAffineUnits.unitsEquiv,
      ``ManuscriptAudit.WeierstrassAffineUnits.unitsEquiv_apply_val,
      ``ManuscriptAudit.WeierstrassAffineUnits.unit_power_surjective] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
