import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaPentagonalSquares
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaPentagonalExpansion

/-! The true Dedekind eta function as its signed unary theta series. -/

namespace ManuscriptAudit.Paper8EtaUnaryTheta

open Function.Periodic Paper8EtaPentagonalSquares Paper8EtaPentagonalExpansion

private theorem q_one_eq_q_twentyFour_pow (z : ℂ) :
    qParam 1 z = qParam 24 z ^ 24 := by
  unfold qParam
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private theorem q_squareIndex (z : ℂ) (k : ℤ) :
    qParam 24 z * qParam 1 z ^ pentagonal k = qParam 24 z ^ (squareIndex k ^ 2) := by
  rw [squareIndex_sq, q_one_eq_q_twentyFour_pow, ← pow_mul, pow_succ']

private theorem characterTwelve_complex (k : ℤ) :
    (characterTwelve (squareIndex k) : ℂ) = (k.negOnePow : ℂ) := by
  by_cases h : Even k
  · have hC : characterTwelve (squareIndex k) = 1 := by
      rw [characterTwelve_squareIndex, Int.negOnePow_even k h]
      rfl
    rw [hC, Int.negOnePow_even k h]
    simp
  · have hO := Int.not_even_iff_odd.mp h
    have hC : characterTwelve (squareIndex k) = -1 := by
      rw [characterTwelve_squareIndex, Int.negOnePow_odd k hO]
      rfl
    rw [hC, Int.negOnePow_odd k hO]
    simp

theorem hasSum_eta_integerSquares (z : UpperHalfPlane) :
    HasSum (fun k : ℤ => (characterTwelve (squareIndex k) : ℂ) *
      qParam 24 z ^ (squareIndex k ^ 2)) (ModularForm.eta z) := by
  let f (m : ℕ) := qParam 24 z * ((PowerSeries.pentagonalSeries ℂ).coeff m * qParam 1 z ^ m)
  have hf : HasSum f (ModularForm.eta z) := hasSum_eta z
  have hZero (m : ℕ) (hm : m ∉ Set.range pentagonal) : f m = 0 := by
    simp [f, PowerSeries.coeff_pentagonalSeries_eq_zero ℂ hm]
  have h := (pentagonal_injective.hasSum_iff hZero).mpr hf
  convert h using 1
  funext k
  unfold f
  simp only [Function.comp_apply, PowerSeries.coeff_pentagonalSeries_pentagonal]
  rw [characterTwelve_complex, ← q_squareIndex z k]
  ring

theorem hasSum_eta_admissibleNaturals (z : UpperHalfPlane) :
    HasSum (fun n : SquareIndices => (characterTwelve n.val : ℂ) * qParam 24 z ^ (n.val ^ 2))
      (ModularForm.eta z) := by
  rw [← squareIndexEquiv.hasSum_iff]
  simpa only [Function.comp_apply, squareIndexEquiv_apply] using hasSum_eta_integerSquares z

/-- Classical unary theta expansion in the actual q^(1/24) coordinate. -/
theorem hasSum_eta_unaryTheta (z : UpperHalfPlane) :
    HasSum (fun n : ℕ => (characterTwelve n : ℂ) * qParam 24 z ^ (n ^ 2)) (ModularForm.eta z) := by
  let f (n : ℕ) := (characterTwelve n : ℂ) * qParam 24 z ^ (n ^ 2)
  have hZ (n : ℕ) (hn : n ∉ Set.range (Subtype.val : SquareIndices → ℕ)) : f n = 0 := by
    have hNo : ¬ (n % 6 = 1 ∨ n % 6 = 5) := fun hc => hn ⟨⟨n, hc⟩, rfl⟩
    have hPos : ¬ (n % 12 = 1 ∨ n % 12 = 11) := by omega
    have hNeg : ¬ (n % 12 = 5 ∨ n % 12 = 7) := by omega
    simp [f, characterTwelve, hPos, hNeg]
  have h := hasSum_eta_admissibleNaturals z
  change HasSum (f ∘ (Subtype.val : SquareIndices → ℕ)) (ModularForm.eta z) at h
  exact (Subtype.val_injective.hasSum_iff hZ).mp h

end ManuscriptAudit.Paper8EtaUnaryTheta

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8EtaUnaryTheta.hasSum_eta_integerSquares,
      ``ManuscriptAudit.Paper8EtaUnaryTheta.hasSum_eta_admissibleNaturals,
      ``ManuscriptAudit.Paper8EtaUnaryTheta.hasSum_eta_unaryTheta] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
