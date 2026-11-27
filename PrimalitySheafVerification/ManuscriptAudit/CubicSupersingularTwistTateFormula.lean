import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicSupersingularSexticTate

/-! Actual prime-adic Frobenius over even-degree fields in supersingular characteristic. -/

namespace ManuscriptAudit.CubicSupersingularTwistTateFormula

open Module WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionCard
open CubicNonsplitThreeAdicTrace PowerTateModule CubicSupersingularUnitFrobenius
open CubicSupersingularTwistFrobenius CubicSexticRotation

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (L : Type*) [Field L] [DecidableEq L] [Algebra (ZMod p) L] [IsAlgClosed L]
variable [Algebra.IsAlgebraic (ZMod p) L]
variable (l : ℕ) [Fact l.Prime]
variable (E : Type*) [Field E] [Fintype E] [Algebra (ZMod p) E] [Algebra E L]

/-- The trace and determinant in the genuine geometric conjugacy to the unit twist. -/
theorem trace_det_for_twist (hp : 5 ≤ p) (hp₃ : p % 3 = 2) (hlp : l ≠ p)
    {m : ℕ} (hm : finrank (ZMod p) E = 2 * m) {A : E}
    (h₂ : (2 : L) ≠ 0) (h₃ : (3 : L) ≠ 0) (hΔ : (shortCubic (0 : L) 1).Δ ≠ 0)
    {v : L} (hv : v ^ 6 = 1) (e : UnitPoints L ≃+ GeometricPoints E L A)
    (he : ∀ P, arithmeticPointFrobenius E L A (e P) =
      e (sexticScale L hv hΔ (arithmeticUnit E L P))) :
    let T := endMap l (arithmeticPointFrobenius E L A)
    let t := twistSign L v * (if v ^ 2 = 1 then (2 : ℤ) else -1) * (-(p : ℤ)) ^ m
    LinearMap.trace ℤ_[l] (Tate l (GeometricPoints E L A)) T = (Int.cast t : ℤ_[l]) ∧
      LinearMap.det T = (Fintype.card E : ℤ_[l]) := by
  let T := endMap l (arithmeticPointFrobenius E L A)
  let k := twistSign L v * (if v ^ 2 = 1 then (2 : ℤ) else -1)
  let U := Tate l (UnitPoints L)
  let B := CubicNonsplitFiniteFieldTate.centeredBasis p L l hp hp₃ hlp one_ne_zero hΔ
  letI := Module.Free.of_basis B
  letI := Module.Finite.of_basis B
  let S := endMap l (sexticScale L hv hΔ)
  let R := endMap l (sexticScale L hv hΔ * arithmeticUnit E L)
  let eT := mapAddEquiv l e
  let c : ℤ_[l] := Int.cast ((-(p : ℤ)) ^ m)
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
  have hScale : R = c • S := by
    have hCast : (algebraMap ℤ_[l] (Module.End ℤ_[l] U)) c =
        Int.cast ((-(p : ℤ)) ^ m) := by
      dsimp only [c]
      rw [map_intCast]
    change endMap l (sexticScale L hv hΔ * arithmeticUnit E L) = c • S
    rw [map_mul, arithmeticUnit_eq_scalar E L p hp hp₃ hm, map_intCast, ← hCast,
      Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]
  have hCard : Fintype.card E = p ^ (2 * m) := by
    rw [Module.card_eq_pow_finrank (K := ZMod p) (V := E), ZMod.card, hm]
  have hC : c ^ 2 = (Fintype.card E : ℤ_[l]) := by
    calc
      _ = ((-(p : ℤ_[l])) ^ m) ^ 2 := by
        simp only [c, Int.cast_pow, Int.cast_neg, Int.cast_natCast]
      _ = ((-(p : ℤ_[l])) ^ 2) ^ m := by
        rw [← pow_mul (-(p : ℤ_[l])) m 2, ← pow_mul (-(p : ℤ_[l])) 2 m, Nat.mul_comm m 2]
      _ = _ := by rw [neg_sq, ← pow_mul, ← Nat.cast_pow, ← hCard]
  have hRank : finrank ℤ_[l] U = 2 := by rw [finrank_eq_card_basis B, Fintype.card_fin]
  obtain ⟨hTrace, hDet⟩ := CubicSupersingularSexticTate.trace_det_formula
    p L l hp hp₃ hlp h₂ h₃ hΔ hv
  change LinearMap.trace ℤ_[l] (Tate l (GeometricPoints E L A)) T =
    (Int.cast (k * (-(p : ℤ)) ^ m) : ℤ_[l]) ∧ LinearMap.det T = (Fintype.card E : ℤ_[l])
  constructor
  · rw [← hConj, LinearMap.trace_conj', hScale, map_smul, hTrace, smul_eq_mul, Int.cast_mul]
    exact mul_comm _ _
  · have hConj' : eT.conj R = eT.toLinearMap ∘ₗ R ∘ₗ eT.symm.toLinearMap := by
      apply LinearMap.ext
      intro x
      rfl
    rw [← hConj, hConj', LinearMap.det_conj, hScale, LinearMap.det_smul, hRank, hDet, mul_one, hC]


end
end ManuscriptAudit.CubicSupersingularTwistTateFormula

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicSupersingularTwistTateFormula.trace_det_for_twist
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
