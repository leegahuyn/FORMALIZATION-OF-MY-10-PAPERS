import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassArithmeticFrobeniusScheme
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleUnitHOneComposition

/-! The actual arithmetic Frobenius square commutes on degree-one unit
cohomology and on the corresponding native Tate modules. -/

namespace ManuscriptAudit.WeierstrassArithmeticFrobeniusUnitSquare

open AlgebraicGeometry CategoryTheory
open WeierstrassProjectiveClosure WeierstrassArithmeticFrobeniusScheme
open OpenEtaleUnitHOneComposition KummerUnitsSheaf PowerTateModule

noncomputable section

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (k K : Type) [Field k] [Fintype k] [Field K] [Algebra k K] [IsAlgClosed K]
variable (W : WeierstrassCurve.Affine k)

private abbrev X := projectiveScheme (W.baseChange K)
private abbrev U := affineScheme (W.baseChange K)
private abbrev G (Y : Scheme.{0}) := Sheaf.H (fullCoordinateUnitSheaf Y) 1
private abbrev j := affineOpen (W.baseChange K)

/-- Pullback by the genuine projective Frobenius, calculated on actual
injective representatives in the small étale site. -/
def projectivePullback : G (X K W) →+ G (X K W) :=
  unitPullback (projectiveFrobenius k K W).hom

/-- Pullback by the genuinely restricted semilinear affine automorphism. -/
def affinePullback : G (U K W) →+ G (U K W) :=
  unitPullback (affineFrobenius k K W).hom

/-- Arithmetic Frobenius commutes with actual restriction of étale units
to the complement of infinity, directly on degree-one cohomology. -/
theorem restrict_projectivePullback :
    (unitPullback (j K W)).comp (projectivePullback k K W) =
      (affinePullback k K W).comp (unitPullback (j K W)) := by
  ext c
  exact unitPullback_comm (j K W) (projectiveFrobenius k K W).hom
    (affineFrobenius k K W).hom (j K W) (affineOpen_projectiveFrobenius k K W) c

variable (l : ℕ) [Fact l.Prime]

/-- The genuine commutative Frobenius square persists on the native
inverse limits of the prime-power torsion subgroups. -/
theorem restrict_projectivePullback_tate :
    (map l (unitPullback (j K W))).comp (map l (projectivePullback k K W)) =
      (map l (affinePullback k K W)).comp (map l (unitPullback (j K W))) := by
  rw [← PowerTateModule.map_comp, ← PowerTateModule.map_comp, restrict_projectivePullback]

end

end ManuscriptAudit.WeierstrassArithmeticFrobeniusUnitSquare

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassArithmeticFrobeniusUnitSquare.restrict_projectivePullback,
      ``ManuscriptAudit.WeierstrassArithmeticFrobeniusUnitSquare.restrict_projectivePullback_tate] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
