import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.FullEtaleHOnePadic
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassProjectiveKummerTate

/-! The true constant-coefficient and twisted prime-adic H¹ modules
of the geometric projective elliptic curve are linearly identified
with its native point Tate module. -/

namespace ManuscriptAudit.WeierstrassProjectiveHOnePadic

open AlgebraicGeometry CategoryTheory
open FullEtaleHOnePadic FullEtaleKummerKernel PowerTorsionTower PowerTateModule
open WeierstrassProjectiveClosure WeierstrassProjectiveUnitTate

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable {K : Type} [Field K] [IsAlgClosed K] [DecidableEq K]
variable (W : WeierstrassCurve.Affine K) [W.IsElliptic]
variable (l : ℕ) [Fact l.Prime] [NeZero (l : K)]

private abbrev X := projectiveScheme W
private abbrev G := Sheaf.H (U (X W)) 1

private theorem globalPower (n : ℕ) :
    Function.Surjective (fun u : (Γ(X W, ⊤))ˣ => u ^ (l ^ n)) := by
  letI : NeZero ((l ^ n : ℕ) : K) :=
    ⟨by rw [Nat.cast_pow]; exact pow_ne_zero n (NeZero.ne (l : K))⟩
  exact WeierstrassProjectiveKummer.globalUnitPower_surjective W (l ^ n)

private def rootsUnitsTate : RootsHOne (X W) l ≃ₗ[ℤ_[l]] Tate l (G W) :=
  PadicBoundedTorsionTower.linearEquiv l
    (FullEtaleKummerTateLimit.Level (X W) l) (FullEtaleKummerTateLimit.step (X W) l)
    (PowerTorsion l (G W)) (transition l (G W))
    (FullEtaleKummerTateLimit.levelEquiv (X W) l (toBase W) (globalPower W l))
    (FullEtaleKummerTateLimit.levelEquiv_step (X W) l (toBase W) (globalPower W l))

/-- The twisted geometric projective étale H¹ is the point Tate module,
with the genuine p-adic scalar action on both sides. -/
def rootsTateLinearEquiv : RootsHOne (X W) l ≃ₗ[ℤ_[l]] Tate l W.Point :=
  let e := ((Sheaf.functorH (X W).smallEtaleTopology 1).mapIso
    (KummerRelativeFull.unitsIso (X := X W) 1)).addCommGroupIsoToAddEquiv
  (rootsUnitsTate W l).trans ((mapAddEquiv l e.symm).trans (unitTateEquiv W l))

private def cyclicToRoots : CyclicHOne (X W) l ≃ₗ[ℤ_[l]] RootsHOne (X W) l :=
  PadicBoundedTorsionTower.linearEquiv l
    (FullEtaleCyclicHOneLimit.Level (X W) l) (FullEtaleCyclicHOneLimit.step (X W) l)
    (FullEtaleKummerTateLimit.Level (X W) l) (FullEtaleKummerTateLimit.step (X W) l)
    (FullEtaleCyclicHOneLimit.levelEquiv (X W) l (toBase W))
    (FullEtaleCyclicHOneLimit.levelEquiv_step (X W) l (toBase W))

/-- The untwisted native geometric projective H¹ is linearly identified
with the point Tate module by the chosen compatible coefficient roots. -/
def cyclicTateLinearEquiv : CyclicHOne (X W) l ≃ₗ[ℤ_[l]] Tate l W.Point :=
  (cyclicToRoots W l).trans (rootsTateLinearEquiv W l)

end

end ManuscriptAudit.WeierstrassProjectiveHOnePadic

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassProjectiveHOnePadic.rootsTateLinearEquiv,
      ``ManuscriptAudit.WeierstrassProjectiveHOnePadic.cyclicTateLinearEquiv] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
