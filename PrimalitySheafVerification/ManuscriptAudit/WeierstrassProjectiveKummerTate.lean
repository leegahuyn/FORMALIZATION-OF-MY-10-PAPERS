import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.FullEtaleKummerTateLimit
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassProjectiveKummer
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassProjectiveUnitTate

/-! The native geometric projective Kummer tower computes the actual
prime-power Tate module of the Weierstrass elliptic curve's point group. -/

namespace ManuscriptAudit.WeierstrassProjectiveKummerTate

open AlgebraicGeometry CategoryTheory
open WeierstrassProjectiveClosure WeierstrassProjectiveKummer
open WeierstrassProjectiveUnitTate PowerTateModule

noncomputable section

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable {K : Type} [Field K] [IsAlgClosed K] [DecidableEq K]
variable (W : WeierstrassCurve.Affine K) [W.IsElliptic]
variable (l : ℕ) [Fact l.Prime] [NeZero (l : K)]

private abbrev X := projectiveScheme W

private theorem global_powers (n : ℕ) :
    Function.Surjective (fun u : (Γ(X W, ⊤))ˣ => u ^ (l ^ n)) := by
  letI : NeZero ((l ^ n : ℕ) : K) :=
    ⟨by rw [Nat.cast_pow]; exact pow_ne_zero n (NeZero.ne (l : K))⟩
  exact globalUnitPower_surjective W (l ^ n)

/-- Genuine twisted first étale Kummer cohomology in the compatible
prime-power limit is the geometric elliptic-curve Tate module. -/
def projectiveRootsTateEquiv :
    ↥(FullEtaleKummerTateLimit.compatible (X W) l) ≃+ Tate l W.Point :=
  (FullEtaleKummerTateLimit.tateEquiv (X W) l (toBase W) (global_powers W l)).trans
    (unitTateEquiv W l).toAddEquiv

end

end ManuscriptAudit.WeierstrassProjectiveKummerTate

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.WeierstrassProjectiveKummerTate.projectiveRootsTateEquiv
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
