import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.FullEtaleKummerKernel
import PrimalitySheafVerification.ManuscriptAudit.PowerTateModule

/-! The compatible limit of the true finite Kummer cohomology groups
is the Tate module of the full étale unit cohomology group. -/

namespace ManuscriptAudit.FullEtaleKummerTateLimit

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open FullEtaleKummerKernel KummerCohomologyDegreeTwo
open TorsionFrobeniusModule PowerTorsionTower PowerTateModule KummerUnitsSheaf

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (X : Scheme.{0}) (l : ℕ) [Fact l.Prime]

private abbrev S := KummerRelativeFull.sequence X

/-- Full small étale degree-one cohomology with literal root-kernel coefficients. -/
abbrev Level (n : ℕ) := Sheaf.H (S X (l ^ n)).X₁ 1

/-- Actual coefficient transitions are induced by the prime-power root map. -/
def step (n : ℕ) : Level X l (n + 1) →+ Level X l n :=
  Sheaf.H.map (rootsStep X (l ^ n) l) 1

/-- The compatible system defining twisted first étale cohomology. -/
def compatible : AddSubgroup (∀ n : ℕ, Level X l n) where
  carrier := {x | ∀ n, step X l n (x (n + 1)) = x n}
  zero_mem' := fun n => map_zero (step X l n)
  add_mem' := by
    intro x y hx hy n
    change step X l n (x (n + 1) + y (n + 1)) = x n + y n
    rw [map_add, hx n, hy n]
  neg_mem' := by
    intro x hx n
    change step X l n (-x (n + 1)) = -x n
    rw [map_neg, hx n]

private abbrev UnitsHOne := Sheaf.H (U X) 1

private def killedByTorsion (G : Type) [AddCommGroup G] (d : ℕ) :
    killedBy G d ≃+ Torsion d G where
  toFun x := ⟨x.val, (mem_iff d G x.val).2 x.property⟩
  invFun x := ⟨x.val, (mem_iff d G x.val).1 x.property⟩
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

variable {K : Type} [Field K] (k : X ⟶ Spec (CommRingCat.of K)) [NeZero (l : K)]
variable (hu : ∀ n : ℕ, Function.Surjective (fun u : (Γ(X, ⊤))ˣ => u ^ (l ^ n)))

private theorem coeff_ne_zero (n : ℕ) : ((l ^ n : ℕ) : K) ≠ 0 := by
  rw [Nat.cast_pow]
  exact pow_ne_zero n (NeZero.ne (l : K))

def levelEquiv (n : ℕ) : Level X l n ≃+ PowerTorsion l (UnitsHOne X) n := by
  letI : NeZero ((l ^ n : ℕ) : K) := ⟨coeff_ne_zero (K := K) l n⟩
  exact (kernelHOneEquiv k (l ^ n) (pow_pos (Fact.out : l.Prime).pos n) (hu n)).trans
    (killedByTorsion (UnitsHOne X) (l ^ n))

theorem levelEquiv_step (n : ℕ) (x : Level X l (n + 1)) :
    levelEquiv X l k hu n (step X l n x) =
      transition l (UnitsHOne X) n (levelEquiv X l k hu (n + 1) x) := by
  letI : NeZero ((l ^ n : ℕ) : K) := ⟨coeff_ne_zero (K := K) l n⟩
  letI : NeZero ((l ^ (n + 1) : ℕ) : K) := ⟨coeff_ne_zero (K := K) l (n + 1)⟩
  apply Subtype.ext
  have h := kernelHOneEquiv_step k (l ^ n) (pow_pos (Fact.out : l.Prime).pos n) (hu n)
    l (pow_pos (Fact.out : l.Prime).pos (n + 1)) (hu (n + 1)) x
  exact congrArg (fun a : killedBy (UnitsHOne X) (l ^ n) => a.val) h

private def internalTateEquiv : ↥(compatible X l) ≃+ Tate l (UnitsHOne X) where
  toFun x := ⟨fun n => levelEquiv X l k hu n (x.val n), fun n => by
    rw [← levelEquiv_step, x.property n]⟩
  invFun x := ⟨fun n => (levelEquiv X l k hu n).symm (x.val n), fun n => by
    apply (levelEquiv X l k hu n).injective
    rw [levelEquiv_step, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, x.property n]⟩
  left_inv x := Subtype.ext (funext fun n => (levelEquiv X l k hu n).symm_apply_apply (x.val n))
  right_inv x := Subtype.ext (funext fun n => (levelEquiv X l k hu n).apply_symm_apply (x.val n))
  map_add' x y := Subtype.ext (funext fun n => (levelEquiv X l k hu n).map_add (x.val n) (y.val n))

/-- The actual compatible finite Kummer cohomology groups compute the
Tate module of degree-one full small étale coordinate-unit cohomology. -/
def tateEquiv : ↥(compatible X l) ≃+ Tate l (Sheaf.H (fullCoordinateUnitSheaf X) 1) :=
  let e := ((Sheaf.functorH X.smallEtaleTopology 1).mapIso
    (KummerRelativeFull.unitsIso (X := X) 1)).addCommGroupIsoToAddEquiv
  (internalTateEquiv X l k hu).trans (mapAddEquiv l e.symm).toAddEquiv

end

end ManuscriptAudit.FullEtaleKummerTateLimit

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.FullEtaleKummerTateLimit.tateEquiv
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
