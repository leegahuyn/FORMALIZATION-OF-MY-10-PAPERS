import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicSexticTateDeterminant

/-! Twisting the coefficient leaves the true 2-adic and 3-adic Frobenius determinant unchanged. -/

namespace ManuscriptAudit.CubicTwistTateDeterminant

open Module WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionCard
open CubicNonsplitThreeAdicTrace PowerTateModule CubicSupersingularUnitFrobenius
open CubicSupersingularTwistFrobenius
open scoped Padic

noncomputable section

variable (E L : Type*) [Field E] [Fintype E] [Field L] [DecidableEq L] [Algebra E L] [IsAlgClosed L]
variable (l : ℕ) [Fact l.Prime]

/-- Genuine relative Frobenius on a nonzero coefficient has the unit twist's determinant. -/
theorem determinant_eq_unit (hl : l = 2 ∨ l = 3)
    (h₂ : (2 : L) ≠ 0) (h₃ : (3 : L) ≠ 0)
    (B : Basis (Fin 2) ℤ_[l] (Tate l (UnitPoints L))) {A : E} (hA : A ≠ 0) :
    LinearMap.det (endMap l (arithmeticPointFrobenius E L A)) =
      LinearMap.det (endMap l (arithmeticUnit E L)) := by
  let T := endMap l (arithmeticPointFrobenius E L A)
  let U := Tate l (UnitPoints L)
  letI := Module.Free.of_basis B
  letI := Module.Finite.of_basis B
  have hΔ := shortCubic_discriminant_ne_zero h₂ h₃ (one_ne_zero : (1 : L) ≠ 0)
  have hΔA := shortCubic_discriminant_ne_zero h₂ h₃ ((map_ne_zero (algebraMap E L)).mpr hA)
  obtain ⟨v, hv, e, he⟩ := exists_twist_conjugacy L E hA hΔ hΔA
  let R := endMap l (sexticScale L hv hΔ * arithmeticUnit E L)
  let eT := mapAddEquiv l e
  have hConj : eT.conj R = T := by
    have h (x : U) : T (eT x) = eT (R x) := by
      apply PowerTateModule.ext l (GeometricPoints E L A)
      intro n
      apply Subtype.ext
      exact he (evaluate l (UnitPoints L) n x : UnitPoints L)
    apply LinearMap.ext
    intro x
    change eT (R (eT.symm x)) = T x
    rw [← h, eT.apply_symm_apply]
  have hConj' : eT.conj R = eT.toLinearMap ∘ₗ R ∘ₗ eT.symm.toLinearMap := by
    apply LinearMap.ext
    intro x
    rfl
  change LinearMap.det T = _
  rw [← hConj, hConj', LinearMap.det_conj]
  change LinearMap.det (endMap l (sexticScale L hv hΔ * arithmeticUnit E L)) = _
  rw [map_mul, map_mul, CubicSexticTateDeterminant.det_sexticScale L l hl h₂ h₃ B hΔ hv, one_mul]

end

end ManuscriptAudit.CubicTwistTateDeterminant

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicTwistTateDeterminant.determinant_eq_unit
  let ax ← collectAxioms name
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  unless ax.all (allowed.contains ·) do
    throwError m!"{name} unexpected axioms {ax}"
  logInfo m!"{name} uses {ax}"
