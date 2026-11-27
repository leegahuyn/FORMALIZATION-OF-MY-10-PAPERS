import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicSupersingularSexticTate

/-! Actual prime-adic Frobenius over even-degree fields in supersingular characteristic. -/

namespace ManuscriptAudit.CubicSupersingularTwistTate

open Module WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionCard
open CubicNonsplitThreeAdicTrace PowerTateModule CubicSupersingularUnitFrobenius
open CubicSupersingularTwistFrobenius

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (L : Type*) [Field L] [DecidableEq L] [Algebra (ZMod p) L] [IsAlgClosed L]
variable [Algebra.IsAlgebraic (ZMod p) L]
variable (l : ℕ) [Fact l.Prime]
variable (E : Type*) [Field E] [Fintype E] [Algebra (ZMod p) E] [Algebra E L]

/-- Every nonzero centered twist over a degree-2m field in this characteristic has
determinant q and actual trace in {2, -2, 1, -1} times (-p)^m. -/
theorem trace_det_even (hp : 5 ≤ p) (hp₃ : p % 3 = 2) (hlp : l ≠ p)
    {m : ℕ} (hm : finrank (ZMod p) E = 2 * m) {A : E} (hA : A ≠ 0) :
    let T := endMap l (arithmeticPointFrobenius E L A)
    ∃ t : ℤ, (t = 2 ∨ t = -2 ∨ t = 1 ∨ t = -1) ∧
      LinearMap.trace ℤ_[l] (Tate l (GeometricPoints E L A)) T =
        (Int.cast (t * (-(p : ℤ)) ^ m) : ℤ_[l]) ∧
      LinearMap.det T = (Fintype.card E : ℤ_[l]) := by
  let T := endMap l (arithmeticPointFrobenius E L A)
  obtain ⟨h₂p, h₃p⟩ := Paper5NonsplitFrobeniusModFour.small_char p (ZMod p) hp
  have h₂ : (2 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap (ZMod p) L)).mpr h₂p
  have h₃ : (3 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap (ZMod p) L)).mpr h₃p
  have hΔ := shortCubic_discriminant_ne_zero h₂ h₃ (one_ne_zero : (1 : L) ≠ 0)
  have hΔA := shortCubic_discriminant_ne_zero h₂ h₃ ((map_ne_zero (algebraMap E L)).mpr hA)
  obtain ⟨v, hv, e, he⟩ := exists_twist_conjugacy L E hA hΔ hΔA
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
        Int.cast ((-(p : ℤ)) ^ m) := map_intCast _ _
    change endMap l (sexticScale L hv hΔ * arithmeticUnit E L) = c • S
    rw [map_mul, arithmeticUnit_eq_scalar E L p hp hp₃ hm, map_intCast, ← hCast,
      Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]
  have hCard : Fintype.card E = p ^ (2 * m) := by
    rw [Module.card_eq_pow_finrank (K := ZMod p) (V := E), ZMod.card, hm]
  have hC : c ^ 2 = (Fintype.card E : ℤ_[l]) := by
    change (Int.cast ((-(p : ℤ)) ^ m) : ℤ_[l]) ^ 2 = _
    rw [Int.cast_pow, Int.cast_neg, Int.cast_natCast, ← pow_mul, mul_comm m 2,
      pow_mul, neg_sq, hCard, Nat.cast_pow, pow_mul]
  have hRank : finrank ℤ_[l] U = 2 := by rw [finrank_eq_card_basis B, Fintype.card_fin]
  obtain ⟨t, ht, hTrace, hDet⟩ := CubicSupersingularSexticTate.trace_det p L l hp hp₃ hlp h₂ h₃ hΔ hv
  change ∃ t : ℤ, (t = 2 ∨ t = -2 ∨ t = 1 ∨ t = -1) ∧
    LinearMap.trace ℤ_[l] (Tate l (GeometricPoints E L A)) T =
      (Int.cast (t * (-(p : ℤ)) ^ m) : ℤ_[l]) ∧
    LinearMap.det T = (Fintype.card E : ℤ_[l])
  refine ⟨t, ht, ?_, ?_⟩
  · rw [← hConj, LinearMap.trace_conj', hScale, map_smul, hTrace, smul_eq_mul, Int.cast_mul]
    exact mul_comm _ _
  · have hConj' : eT.conj R = eT.toLinearMap ∘ₗ R ∘ₗ eT.symm.toLinearMap := by
      apply LinearMap.ext
      intro x
      rfl
    rw [← hConj, hConj', LinearMap.det_conj, hScale, LinearMap.det_smul, hRank, hDet, mul_one, hC]

end
end ManuscriptAudit.CubicSupersingularTwistTate

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicSupersingularTwistTate.trace_det_even
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
