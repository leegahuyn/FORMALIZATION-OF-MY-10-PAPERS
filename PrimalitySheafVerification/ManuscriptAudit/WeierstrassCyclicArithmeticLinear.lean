import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.FullEtaleCyclicUnitTateLinear
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassCyclicArithmeticAction
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassProjectivePointFrobeniusTate

/-! The genuine cyclotomic relation between unit Tate arithmetic
Frobenius and untwisted étale arithmetic Frobenius is linear. -/

namespace ManuscriptAudit.WeierstrassCyclicArithmeticLinear

open AlgebraicGeometry CategoryTheory Module
open KummerUnitsSheaf FullEtaleHOnePadic FullEtaleCyclicUnitTateLinear
open WeierstrassProjectiveClosure WeierstrassProjectiveKummer
open WeierstrassCyclicArithmeticAction WeierstrassProjectivePointFrobeniusTate
open PowerTateModule
open scoped Padic

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

private abbrev V {k : Type} [Field k] (K : Type) [Field K] [Algebra k K]
    (W : WeierstrassCurve.Affine k) := W.baseChange K
private abbrev X {k : Type} [Field k] (K : Type) [Field K] [Algebra k K]
    (W : WeierstrassCurve.Affine k) := projectiveScheme (V K W)
private abbrev H {k : Type} [Field k] (K : Type) [Field K] [Algebra k K]
    (W : WeierstrassCurve.Affine k) :=
  Sheaf.H (fullCoordinateUnitSheaf (X K W)) 1

variable {k : Type} [Field k]
variable (K : Type) [Field K] [Algebra k K] [IsAlgClosed K] [DecidableEq K]
variable (W : WeierstrassCurve.Affine k) [W.IsElliptic]
variable (l : ℕ) [Fact l.Prime] [NeZero (l : K)]

private theorem globalPowers (n : ℕ) :
    Function.Surjective (fun u : (Γ(X K W, ⊤))ˣ => u ^ (l ^ n)) := by
  letI : NeZero ((l ^ n : ℕ) : K) :=
    ⟨by rw [Nat.cast_pow]; exact pow_ne_zero n (NeZero.ne (l : K))⟩
  exact globalUnitPower_surjective (V K W) (l ^ n)

/-- The actual projective cyclic–unit Kummer identification is linear. -/
def comparison : CyclicHOne (X K W) l ≃ₗ[ℤ_[l]] Tate l (H K W) :=
  cyclicUnitTateLinearEquiv (X K W) l (toBase (V K W)) (globalPowers K W l)

variable (k) [Fintype k]

/-- On genuine projective cohomology, the unit Tate operator is the
linear conjugate of the cyclic arithmetic operator times the field size. -/
theorem unitAction_eq_cyclic_smul :
    projectiveUnitAction k K W l =
      (Fintype.card k : ℤ_[l]) • (comparison K W l).conj (cyclicFrobenius l k K W) := by
  let e := comparison K W l
  apply LinearMap.ext
  intro x
  let y := e.symm x
  have h : projectiveUnitAction k K W l (e y) =
      Fintype.card k • e (cyclicFrobenius l k K W y) :=
    cyclicFrobenius_twist l k K W y
  have hy : e y = x := e.apply_symm_apply x
  rw [hy] at h
  change projectiveUnitAction k K W l x =
    (Fintype.card k : ℤ_[l]) • e (cyclicFrobenius l k K W y)
  rw [Nat.cast_smul_eq_nsmul]
  exact h

end

end ManuscriptAudit.WeierstrassCyclicArithmeticLinear

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.WeierstrassCyclicArithmeticLinear.unitAction_eq_cyclic_smul
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
