import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper9CompactResolventObstruction
import PrimalitySheafVerification.ManuscriptAudit.Paper9ResidualVector

/-! A realization agreeing with the exact shifted cusp differential has no compact left inverse. -/

namespace ManuscriptAudit.Paper9ResidualCompactInverse

open Paper9CuspWaveHilbert Paper9ResidualVector Paper9CompactResolventObstruction
open Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry

noncomputable section

theorem no_compact_inverse_for_cusp_differential (D : GammaTwoFundamentalDomain)
    (T : quotientL2 D →ₗ.[ℂ] quotientL2 D) (k : ℝ) (μ : ℂ)
    (hDomain : ∀ R (hR : 1 ≤ R), waveVector D k R (zero_lt_one.trans_le hR) ∈ T.domain)
    (hAction : ∀ R (hR : 1 ≤ R),
      T ⟨waveVector D k R (zero_lt_one.trans_le hR), hDomain R hR⟩ -
        (-((1 / 4 + k ^ 2 : ℝ) : ℂ)) • waveVector D k R (zero_lt_one.trans_le hR) =
      residualVector D k R (zero_lt_one.trans_le hR)) :
    ¬ ∃ B : quotientL2 D →L[ℂ] quotientL2 D,
      IsCompactOperator (B : quotientL2 D →ₗ[ℂ] quotientL2 D) ∧
      ∀ v : T.domain, B (T v - μ • (v : quotientL2 D)) = v := by
  apply no_compact_resolvent_inverse D T k μ hDomain
  intro R hR
  rw [hAction R hR]
  exact residualVector_norm_sq D k R (zero_lt_one.trans_le hR)

end
end ManuscriptAudit.Paper9ResidualCompactInverse

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper9ResidualCompactInverse.no_compact_inverse_for_cusp_differential
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
