import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8SpectralCrossBlocks
import PrimalitySheafVerification.ManuscriptAudit.Paper8IsolatedCauchyPole

/-! Any nonzero complete discrete cross pairing forces a genuine pole of its cross resolvent. -/

namespace ManuscriptAudit.Paper8SpectralCrossPole

open Paper8SpectralCrossBlocks Paper8IsolatedCauchyPole
open scoped InnerProductSpace

noncomputable section

theorem exists_simple_cross_resolvent_pole {H I Λ : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (b : HilbertBasis I ℂ H)
    (label : I → Λ) (w : Λ → ℂ)
    (hIso : ∀ λ : Λ, ∃ r > (0 : ℝ), ∀ μ, μ ≠ λ → r ≤ ‖w μ - w λ‖)
    {x y : H} (hxy : ⟪x, y⟫_ℂ ≠ 0) :
    ∃ λ : Λ,
      MeromorphicAt (cauchySpectralSeries w (crossSpectralBlock b label x y)) (w λ) ∧
      meromorphicOrderAt (cauchySpectralSeries w (crossSpectralBlock b label x y)) (w λ) = (-1 : ℤ) := by
  obtain ⟨λ, hλ⟩ := exists_nonzero_crossSpectralBlock b label hxy
  obtain ⟨r, hr, hs⟩ := hIso λ
  exact ⟨λ, cauchySpectralSeries_simple_pole w _ (summable_norm_crossSpectralBlock b label x y)
    λ hλ hr hs⟩

end
end ManuscriptAudit.Paper8SpectralCrossPole

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper8SpectralCrossPole.exists_simple_cross_resolvent_pole
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
