import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaCosetMass
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaCriticalOddVanishing
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaPhaseCocycle

/-! The finite chart family for the odd eta law transforms by unitary phase and coset permutation. -/

namespace ManuscriptAudit.Paper8OddCosetChartTransition

open UpperHalfPlane
open Paper8EtaCosetMass FiniteIndexWeightZeroCosets Paper8EtaCriticalOddVanishing
open Paper8EtaHalfWeightPhase Paper8EtaPhaseCocycle Paper8OddCrossCuspRows
open Paper8EtaInverseWeightedVanishing (levelCharacter_sq)
open scoped MatrixGroups

noncomputable section

abbrev levelFourRightCoset := RightCoset (CongruenceSubgroup.Gamma0 4)

def oddCosetChart (F : ℂ → ℂ) (q : levelFourRightCoset) (z : ℍ) : ℂ :=
  let a := cellRepresentative (CongruenceSubgroup.Gamma0 4) q
  (negativePhase a z)⁻¹ * F (a • z : ℍ)

private theorem negativePhase_ne_zero (g : SL(2, ℤ)) (z : ℍ) : negativePhase g z ≠ 0 := by
  intro h
  have hn := negativePhase_norm g z
  simp only [h, norm_zero, zero_ne_one] at hn

private theorem coset_transition_member (q : levelFourRightCoset) (g : SL(2, ℤ)) :
    cellRepresentative (CongruenceSubgroup.Gamma0 4) q * g *
      (cellRepresentative (CongruenceSubgroup.Gamma0 4)
        (rightCosetMul (CongruenceSubgroup.Gamma0 4) g q))⁻¹ ∈ CongruenceSubgroup.Gamma0 4 := by
  let H := CongruenceSubgroup.Gamma0 4
  let a := cellRepresentative H q
  let b := cellRepresentative H (rightCosetMul H g q)
  have hSlide : rightCosetMul H g (rightCosetMk H a) = rightCosetMk H (a * g) := rfl
  have hRel : rightCosetMk H (a * g) = rightCosetMk H b := by
    rw [← hSlide, cellRepresentative_mk, cellRepresentative_mk]
  exact QuotientGroup.rightRel_apply.mp (Quotient.exact hRel.symm)

def levelFourChartTransition (q : levelFourRightCoset) (g : SL(2, ℤ)) :
    CongruenceSubgroup.Gamma0 4 :=
  ⟨_, coset_transition_member q g⟩

theorem oddCosetChart_transform {F : ℂ → ℂ} (hF : OddMaassLaw F)
    (q : levelFourRightCoset) (g : SL(2, ℤ)) (z : ℍ) :
    oddCosetChart F q (g • z) =
      (levelCharacter (levelFourChartTransition q g) : ℂ) * negativePhase g z *
        oddCosetChart F (rightCosetMul (CongruenceSubgroup.Gamma0 4) g q) z := by
  let H := CongruenceSubgroup.Gamma0 4
  let a := cellRepresentative H q
  let r := rightCosetMul H g q
  let b := cellRepresentative H r
  let h := levelFourChartTransition q g
  have hMul : (h : SL(2, ℤ)) * b = a * g := by
    change (a * g * b⁻¹) * b = a * g
    rw [mul_assoc, inv_mul_cancel, mul_one]
  have hAct : a • (g • z) = (h : SL(2, ℤ)) • (b • z) := by
    rw [← mul_smul, ← mul_smul, hMul]
  have hPhase := congrArg (fun k : SL(2, ℤ) => negativePhase k z) hMul
  simp only [negativePhase_mul] at hPhase
  have hRatio : (negativePhase a (g • z))⁻¹ * negativePhase (h : SL(2, ℤ)) (b • z) =
      negativePhase g z * (negativePhase b z)⁻¹ := by
    have ha := negativePhase_ne_zero a (g • z)
    have hb := negativePhase_ne_zero b z
    apply mul_right_cancel₀ hb
    calc
      _ = (negativePhase a (g • z))⁻¹ *
          (negativePhase (h : SL(2, ℤ)) (b • z) * negativePhase b z) := by rw [mul_assoc]
      _ = (negativePhase a (g • z))⁻¹ *
          (negativePhase a (g • z) * negativePhase g z) := by rw [hPhase]
      _ = negativePhase g z := by rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]
      _ = _ := by rw [mul_assoc, inv_mul_cancel₀ hb, mul_one]
  change (negativePhase a (g • z))⁻¹ * F (a • (g • z) : ℍ) =
    (levelCharacter h : ℂ) * negativePhase g z * ((negativePhase b z)⁻¹ * F (b • z : ℍ))
  rw [hAct, hF h (b • z)]
  calc
    _ = ((negativePhase a (g • z))⁻¹ * negativePhase (h : SL(2, ℤ)) (b • z)) *
        ((levelCharacter h : ℂ) * F (b • z : ℍ)) := by ring
    _ = _ := by rw [hRatio]; ring

theorem norm_oddCosetChart (F : ℂ → ℂ) (q : levelFourRightCoset) (z : ℍ) :
    ‖oddCosetChart F q z‖ = ‖F (cellRepresentative (CongruenceSubgroup.Gamma0 4) q • z : ℍ)‖ := by
  unfold oddCosetChart
  rw [norm_mul, norm_inv, negativePhase_norm, inv_one, one_mul]

theorem norm_oddCosetChart_transform {F : ℂ → ℂ} (hF : OddMaassLaw F)
    (q : levelFourRightCoset) (g : SL(2, ℤ)) (z : ℍ) :
    ‖oddCosetChart F q (g • z)‖ =
      ‖oddCosetChart F (rightCosetMul (CongruenceSubgroup.Gamma0 4) g q) z‖ := by
  let h := levelFourChartTransition q g
  have hSq : ‖(levelCharacter h : ℂ)‖ ^ 2 = 1 := by
    rw [← norm_pow, levelCharacter_sq, norm_one]
  have hNorm : ‖(levelCharacter h : ℂ)‖ = 1 := by
    nlinarith [norm_nonneg (levelCharacter h : ℂ)]
  rw [oddCosetChart_transform hF, norm_mul, norm_mul, negativePhase_norm]
  change ‖(levelCharacter h : ℂ)‖ * 1 * _ = _
  rw [hNorm, one_mul, one_mul]

def oddCosetChartMassAt (F : ℂ → ℂ) (z : ℍ) : ℝ :=
  letI := rightCosetFintype (CongruenceSubgroup.Gamma0 4)
  ∑ q : levelFourRightCoset, ‖oddCosetChart F q z‖ ^ 2

theorem oddCosetChartMassAt_invariant {F : ℂ → ℂ} (hF : OddMaassLaw F)
    (g : SL(2, ℤ)) (z : ℍ) :
    oddCosetChartMassAt F (g • z) = oddCosetChartMassAt F z := by
  let H := CongruenceSubgroup.Gamma0 4
  letI := rightCosetFintype H
  unfold oddCosetChartMassAt
  refine Fintype.sum_equiv (rightCosetMul H g) _ _ (fun q => ?_)
  exact congrArg (fun r : ℝ => r ^ 2) (norm_oddCosetChart_transform hF q g z)

end
end ManuscriptAudit.Paper8OddCosetChartTransition

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8OddCosetChartTransition.oddCosetChart_transform,
      ``ManuscriptAudit.Paper8OddCosetChartTransition.oddCosetChartMassAt_invariant] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
