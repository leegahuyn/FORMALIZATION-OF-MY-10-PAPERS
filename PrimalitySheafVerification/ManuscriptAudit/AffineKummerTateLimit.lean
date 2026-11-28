import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineKummerTorsionTransition
import PrimalitySheafVerification.ManuscriptAudit.PowerTateModule

/-! The inverse limit of actual affine Kummer H¹ is the Tate module of native unit H¹. -/

namespace ManuscriptAudit.AffineKummerTateLimit

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open KummerSheafSequence KummerCohomologySequence KummerCohomologyDegreeTwo
open WeierstrassAffineKummer AffineKummerTorsionTransition
open TorsionFrobeniusModule PowerTorsionTower PowerTateModule

noncomputable section

attribute [local instance] affineSiteHasExt

set_option backward.isDefEq.respectTransparency false

variable (R : CommRingCat.{0}) (l : ℕ) [Fact l.Prime]

/-- Degree-one cohomology of the actual affine Kummer root kernel at a fixed power. -/
abbrev Level (n : ℕ) := Sheaf.H (powerKernel R (l ^ n)) 1

/-- The transition in degree one comes from the literal root power morphism. -/
def step (n : ℕ) : Level R l (n + 1) →+ Level R l n :=
  Sheaf.H.map (rootsTransition R (l ^ n) l) 1

/-- Actual compatible additive tuples of the derived Kummer cohomology groups. -/
def compatible : AddSubgroup (∀ n : ℕ, Level R l n) where
  carrier := {x | ∀ n, step R l n (x (n + 1)) = x n}
  zero_mem' := fun n => map_zero (step R l n)
  add_mem' := by
    intro x y hx hy n
    change step R l n (x (n + 1) + y (n + 1)) = x n + y n
    rw [map_add, hx n, hy n]
  neg_mem' := by
    intro x hx n
    change step R l n (-x (n + 1)) = -x n
    rw [map_neg, hx n]

private abbrev UnitHOne := Sheaf.H (unitSheaf (Spec R)) 1

private def killedByTorsion (G : Type) [AddCommGroup G] (d : ℕ) :
    killedBy G d ≃+ Torsion d G where
  toFun x := ⟨x.val, (mem_iff d G x.val).2 x.property⟩
  invFun x := ⟨x.val, (mem_iff d G x.val).1 x.property⟩
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext rfl
  map_add' x y := Subtype.ext rfl

variable (hUnit : ∀ n : ℕ, IsUnit ((l ^ n : ℕ) : R))
variable (hPow : ∀ n : ℕ, Function.Surjective (fun u : Rˣ => u ^ (l ^ n)))

private def levelEquiv (n : ℕ) : Level R l n ≃+ PowerTorsion l (UnitHOne R) n :=
  (degreeOneKernelEquiv R (l ^ n) (pow_pos (Fact.out : l.Prime).pos n) (hUnit n) (hPow n)).trans
    (killedByTorsion (UnitHOne R) (l ^ n))

private theorem levelEquiv_step (n : ℕ) (x : Level R l (n + 1)) :
    levelEquiv R l hUnit hPow n (step R l n x) =
      transition l (UnitHOne R) n (levelEquiv R l hUnit hPow (n + 1) x) := by
  apply Subtype.ext
  have h := degreeOneKernelEquiv_transition R (l ^ n) l
    (pow_pos (Fact.out : l.Prime).pos n) (pow_pos (Fact.out : l.Prime).pos (n + 1))
    (hUnit n) (hUnit (n + 1)) (hPow n) (hPow (n + 1)) x
  exact congrArg (fun a : killedBy (UnitHOne R) (l ^ n) => a.val) h

/-- For affine rings with surjective ℓ-power on units, the actual coefficient-root
H¹ inverse limit is the Tate module of the genuine first unit cohomology. -/
def tateEquiv : ↥(compatible R l) ≃+ Tate l (UnitHOne R) where
  toFun x := ⟨fun n => levelEquiv R l hUnit hPow n (x.val n), fun n => by
    rw [← levelEquiv_step, x.property n]⟩
  invFun x := ⟨fun n => (levelEquiv R l hUnit hPow n).symm (x.val n), fun n => by
    apply (levelEquiv R l hUnit hPow n).injective
    rw [levelEquiv_step, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, x.property n]⟩
  left_inv x := Subtype.ext (funext fun n => (levelEquiv R l hUnit hPow n).symm_apply_apply (x.val n))
  right_inv x := Subtype.ext (funext fun n => (levelEquiv R l hUnit hPow n).apply_symm_apply (x.val n))
  map_add' x y := Subtype.ext (funext fun n => (levelEquiv R l hUnit hPow n).map_add (x.val n) (y.val n))

end

end ManuscriptAudit.AffineKummerTateLimit

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineKummerTateLimit.tateEquiv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
