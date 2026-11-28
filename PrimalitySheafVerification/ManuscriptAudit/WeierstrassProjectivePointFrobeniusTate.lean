import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassArithmeticAffineHOnePoint
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassProjectiveActualUnitRestriction
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassProjectiveUnitTate
import PrimalitySheafVerification.ManuscriptAudit.CharpolyInjectiveIntertwiner

/-! The actual projective étale unit Tate Frobenius and the literal
geometric-point Tate Frobenius have the same integral characteristic polynomial. -/

namespace ManuscriptAudit.WeierstrassProjectivePointFrobeniusTate

open AlgebraicGeometry CategoryTheory Module
open PowerTateModule KummerUnitsSheaf OpenEtaleUnitHOneComposition
open WeierstrassProjectiveClosure WeierstrassArithmeticFrobeniusScheme
open WeierstrassArithmeticAffineHOnePoint WeierstrassArithmeticPicardFrobenius
open WeierstrassProjectiveActualUnitRestriction WeierstrassProjectiveUnitTate
open scoped Padic

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

private abbrev V {k : Type} [Field k] (K : Type) [Field K] [Algebra k K]
    (W : WeierstrassCurve.Affine k) := W.baseChange K
private abbrev H {k : Type} [Field k] (K : Type) [Field K] [Algebra k K]
    (W : WeierstrassCurve.Affine k) :=
  Sheaf.H (fullCoordinateUnitSheaf (projectiveScheme (V K W))) 1

variable {k : Type} [Field k]
variable (K : Type) [Field K] [Algebra k K] [IsAlgClosed K] [DecidableEq K]
variable (W : WeierstrassCurve.Affine k) [W.IsElliptic]
variable (l : ℕ) [Fact l.Prime]

private abbrev j {k : Type} [Field k] (K : Type) [Field K] [Algebra k K]
    (W : WeierstrassCurve.Affine k) := affineOpen (V K W)

/-- Map actual point classes via the full-site Picard comparison. -/
def unitHOneToPoint : H K W →+ (V K W).Point :=
  (affineHOneToPoint K W).comp (unitPullback (j K W))

/-- The genuine comparison to the geometric Tate points is injective. -/
def unitTateToPoint : Tate l (H K W) →ₗ[ℤ_[l]] Tate l (V K W).Point :=
  map l (unitHOneToPoint K W)

theorem unitTateToPoint_injective : Function.Injective (unitTateToPoint K W l) := by
  change Function.Injective (map l ((affineHOneToPoint K W).comp (unitPullback (j K W))))
  rw [PowerTateModule.map_comp]
  exact (map_injective l (affineHOneToPoint K W) (affineHOneToPoint_injective K W)).comp
    (unitRestrictionTate_bijective (V K W) l).injective

variable (k) [Fintype k]

/-- Genuine arithmetic pullback on the projective unit Tate module. -/
def projectiveUnitAction : Module.End ℤ_[l] (Tate l (H K W)) :=
  map l (unitPullback (projectiveFrobenius k K W).hom)

/-- The native action on the true geometric point Tate module. -/
def pointAction : Module.End ℤ_[l] (Tate l (V K W).Point) :=
  map l (arithmeticPoint k K W)

/-- The genuine affine Picard comparison intertwines the two arithmetic
Frobenius operators on their actual Tate modules. -/
theorem unitTateToPoint_intertwines :
    (unitTateToPoint K W l).comp (projectiveUnitAction k K W l) =
      (pointAction k K W l).comp (unitTateToPoint K W l) := by
  apply LinearMap.ext
  intro x
  apply PowerTateModule.ext l (V K W).Point
  intro n
  apply Subtype.ext
  let a : H K W := (x.val n).val
  let i := affineOpen (V K W)
  let f := (projectiveFrobenius k K W).hom
  let g := (affineFrobenius k K W).hom
  change affineHOneToPoint K W (unitPullback i (unitPullback f a)) =
    arithmeticPoint k K W (affineHOneToPoint K W (unitPullback i a))
  have h := unitPullback_comm i f g i (affineOpen_projectiveFrobenius k K W) a
  exact (congrArg (affineHOneToPoint K W) h).trans
    (affineHOneToPoint_frobenius k K W (unitPullback i a))

/-- The characteristic polynomial on actual projective unit Tate H¹
is the true point-Tate characteristic polynomial. -/
theorem projectiveUnitAction_charpoly (b : Basis (Fin 2) ℤ_[l] (Tate l (V K W).Point)) :
    (projectiveUnitAction k K W l).charpoly = (pointAction k K W l).charpoly := by
  let a := b.map (unitTateEquiv (V K W) l).symm
  exact CharpolyInjectiveIntertwiner.charpoly_eq a b _ _ (unitTateToPoint K W l)
    (unitTateToPoint_injective K W l) (unitTateToPoint_intertwines k K W l)

end

end ManuscriptAudit.WeierstrassProjectivePointFrobeniusTate

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassProjectivePointFrobeniusTate.unitTateToPoint_injective,
      ``ManuscriptAudit.WeierstrassProjectivePointFrobeniusTate.unitTateToPoint_intertwines,
      ``ManuscriptAudit.WeierstrassProjectivePointFrobeniusTate.projectiveUnitAction_charpoly] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
