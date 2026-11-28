import Lean.Util.CollectAxioms
import Mathlib.Analysis.RCLike.Sqrt
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaPhaseCocycle
import PrimalitySheafVerification.ManuscriptAudit.Paper8ActualEtaDedekindMultiplier
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossCuspCutoff

/-! The finite odd cross-cusp sum expressed in the genuine level-four eta automorphy and its conjugated Kloosterman factor. -/

namespace ManuscriptAudit.Paper8OddCrossCuspActualMultiplier

open UpperHalfPlane
open Paper8ActualEtaSquaredModularity Paper8EtaPositiveLowerLeftMultiplier
open Paper8EtaHalfWeightPhase Paper8EtaPhaseCocycle Paper8ActualEtaDedekindMultiplier
open Paper8OddCrossCuspRows Paper8OddCrossCuspNormalization Paper8OddCrossCuspPhase
open Paper8OddCrossCuspCutoff Paper8NormalizedKloostermanRows
open Paper8HolomorphicPartPhase (periodCoefficient)
open scoped MatrixGroups

noncomputable section

def crossGroupElement {D : ℕ} (A : CrossRow D) : CongruenceSubgroup.Gamma0 4 :=
  ⟨A.matrix * ModularGroup.S⁻¹, A.atLevel⟩

theorem crossGroupElement_mul_S {D : ℕ} (A : CrossRow D) :
    (crossGroupElement A : SL(2, ℤ)) * ModularGroup.S = A.matrix := by
  simp only [crossGroupElement, mul_assoc, inv_mul_cancel, mul_one]

theorem crossGroupElement_character {D : ℕ} (A : CrossRow D) :
    levelCharacter (crossGroupElement A) = chiFour (D : ZMod 4) := by
  have h := (cuspTranslate_entries A.matrix 0).2
  have hD : (crossGroupElement A : SL(2, ℤ)) 1 1 = (D : ℤ) := by
    simpa only [crossGroupElement, cuspTranslate, zpow_zero, mul_one, A.lowerLeft] using h
  rw [levelCharacter_apply, hD, Int.cast_natCast]

private theorem negativeSquareRootPhase_ne_zero (g : SL(2, ℤ)) (z : ℍ) :
    negativeSquareRootPhase g z ≠ 0 := by
  have hd := denominator_ne_zero g z
  have hD : Complex.sqrt (denominator g z) ≠ 0 := by
    rw [sqrt_eq_exp hd]
    exact Complex.exp_ne_zero _
  have hN : (Real.sqrt ‖denominator g z‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (norm_pos_iff.mpr hd)).ne'
  have hNorm : (‖denominator g z‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hd)
  exact mul_ne_zero (div_ne_zero hD hN) (div_ne_zero hNorm hd)

private theorem principalEtaMultiplier_ne_zero (g : SL(2, ℤ)) : principalEtaMultiplier g ≠ 0 := by
  intro h
  have hPow := principalEtaMultiplier_pow_twentyFour g
  rw [h, zero_pow (by decide : (24 : ℕ) ≠ 0)] at hPow
  exact zero_ne_one hPow

def analyticCrossEntry {D : ℕ} (A : CrossRow D) (z : ℍ) : ℂ :=
  (starRingEnd ℂ) (oddEtaPhase (crossGroupElement A) (ModularGroup.S • z)) *
    (starRingEnd ℂ) (negativeSquareRootPhase ModularGroup.S z / negativeSquareRootPhase A.matrix z) *
      Complex.exp (periodCoefficient * (scaledCrossDiagonal D (A.matrix 0 0) (A.matrix 1 1) : ℂ))

theorem analyticCrossEntry_eq {D : ℕ} (hD : 0 < D) (A : CrossRow D) (z : ℍ) :
    analyticCrossEntry A z = crossEntry D (A.matrix 0 0) (A.matrix 1 1) := by
  have hA : 0 < A.matrix 1 0 := by rw [A.lowerLeft]; exact_mod_cast hD
  have hS : 0 < ModularGroup.S 1 0 := by norm_num [ModularGroup.coe_S]
  have hOne (g : SL(2, ℤ)) (hg : 0 < g 1 0) :
      negativePhase g z = principalEtaMultiplier g * negativeSquareRootPhase g z :=
    negativePhase_principal g hg z
  rw [analyticCrossEntry, oddEtaPhase_cross, crossGroupElement_mul_S, crossGroupElement_character,
    hOne A.matrix hA, hOne ModularGroup.S hS, crossEntry_eq_actualPrincipalEta A.matrix A.lowerLeft hD]
  simp only [map_mul, map_div₀, map_intCast]
  have hGeomA : (starRingEnd ℂ) (negativeSquareRootPhase A.matrix z) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).2 (negativeSquareRootPhase_ne_zero A.matrix z)
  have hGeomS : (starRingEnd ℂ) (negativeSquareRootPhase ModularGroup.S z) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).2 (negativeSquareRootPhase_ne_zero ModularGroup.S z)
  have hNuS : (starRingEnd ℂ) (principalEtaMultiplier ModularGroup.S) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).2 (principalEtaMultiplier_ne_zero ModularGroup.S)
  field_simp [hGeomA, hGeomS, hNuS] <;> ring

@[instance_reducible] def analyticCrossFintype {D : ℕ} (hD : 0 < D) (hOdd : Odd D) :
    Fintype (CrossRow D) :=
  Fintype.ofEquiv (ReducedResidue D) ((rowsEquiv hD).symm.trans (crossRowsEquiv hD hOdd))

theorem crossSum_eq_analytic {D : ℕ} (hD : 0 < D) (hOdd : Odd D) (z : ℍ) :
    letI := analyticCrossFintype hD hOdd
    crossSum hD = ∑ A : CrossRow D, analyticCrossEntry A z := by
  letI := analyticCrossFintype hD hOdd
  unfold crossSum
  rw [dif_pos hOdd]
  refine Fintype.sum_equiv (Equiv.refl (CrossRow D)) _ _ (fun A => ?_)
  exact (analyticCrossEntry_eq hD A z).symm

end
end ManuscriptAudit.Paper8OddCrossCuspActualMultiplier

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8OddCrossCuspActualMultiplier.crossSum_eq_analytic
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
