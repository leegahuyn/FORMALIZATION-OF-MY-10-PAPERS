import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.FullEtaleKummerConstantTransition
import PrimalitySheafVerification.ManuscriptAudit.FullEtaleKummerTateLimit
import PrimalitySheafVerification.ManuscriptAudit.CyclicPowerInverseLimit

/-! A coherent system of primitive roots identifies the actual untwisted
finite cyclic étale tower with the actual twisted Kummer tower. -/

namespace ManuscriptAudit.FullEtaleCyclicHOneLimit

open AlgebraicGeometry CategoryTheory
open EtaleKummerCyclicCoordinates FullEtaleKummerConstantTransition FullEtaleKummerKernel

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (X : Scheme.{0}) (l : ℕ)

private abbrev C := AddCommGrpCat.{0}
private abbrev F := constantSheaf X.smallEtaleTopology C

/-- Sheafification of the literal finite cyclic coefficients at level n. -/
abbrev coefficients (n : ℕ) := (F X).obj (cyclicGroup l n)

/-- Actual H¹ of the finite cyclic coefficient sheaf. -/
abbrev Level (n : ℕ) := Sheaf.H (coefficients X l n) 1

/-- Cohomology transition from reduction of the actual cyclic coefficients. -/
def step (n : ℕ) : Level X l (n + 1) →+ Level X l n :=
  Sheaf.H.map ((F X).map (reduction l n)) 1

/-- Compatible H¹ with the genuine constant ℤ/ℓⁿ coefficient system. -/
def compatible : AddSubgroup (∀ n : ℕ, Level X l n) :=
  CyclicPowerInverseLimit.compatibleTuples (Level X l) (step X l)

variable {K : Type} [Field K] [IsAlgClosed K]
variable (k : X ⟶ Spec (CommRingCat.of K)) [Fact l.Prime] [NeZero (l : K)]

private def levelIso (n : ℕ) :
    coefficients X l n ≅ (KummerRelativeFull.sequence X (l ^ n)).X₁ :=
  (F X).mapIso (cyclicIso K l n) ≪≫ constantKernelIso k l n

private theorem levelIso_step (n : ℕ) :
    (F X).map (reduction l n) ≫ (levelIso X l k n).hom =
      (levelIso X l k (n + 1)).hom ≫ rootsStep X (l ^ n) l := by
  let b := (constantKernelIso k l n).hom
  let a := (constantKernelIso k l (n + 1)).hom
  let q := F X
  have h : q.map (reduction l n) ≫ q.map (cyclicIso K l n).hom =
      q.map (cyclicIso K l (n + 1)).hom ≫ q.map (coefficientStep K l n) := by
    rw [← Functor.map_comp, ← Functor.map_comp, cyclicIso_step]
  change q.map (reduction l n) ≫ q.map (cyclicIso K l n).hom ≫ b =
    (q.map (cyclicIso K l (n + 1)).hom ≫ a) ≫ rootsStep X (l ^ n) l
  rw [← Category.assoc, h, Category.assoc, constantKernelIso_step, Category.assoc]

def levelEquiv (n : ℕ) :
    Level X l n ≃+ FullEtaleKummerTateLimit.Level X l n :=
  ((Sheaf.functorH X.smallEtaleTopology 1).mapIso (levelIso X l k n)).addCommGroupIsoToAddEquiv

theorem levelEquiv_step (n : ℕ) (x : Level X l (n + 1)) :
    levelEquiv X l k n (step X l n x) =
      FullEtaleKummerTateLimit.step X l n (levelEquiv X l k (n + 1) x) := by
  change Sheaf.H.map (levelIso X l k n).hom 1
    (Sheaf.H.map ((F X).map (reduction l n)) 1 x) =
    Sheaf.H.map (rootsStep X (l ^ n) l) 1
      (Sheaf.H.map (levelIso X l k (n + 1)).hom 1 x)
  rw [← Sheaf.H.map_comp_apply, levelIso_step, Sheaf.H.map_comp_apply]

/-- The native untwisted compatible H¹ identifies with the native Kummer
root tower after choosing the coherent coefficient roots. -/
def rootsEquiv : ↥(compatible X l) ≃+ ↥(FullEtaleKummerTateLimit.compatible X l) where
  toFun x := ⟨fun n => levelEquiv X l k n (x.val n), fun n => by
    rw [← levelEquiv_step]
    exact congrArg (levelEquiv X l k n) (x.property n)⟩
  invFun x := ⟨fun n => (levelEquiv X l k n).symm (x.val n), fun n => by
    apply (levelEquiv X l k n).injective
    rw [levelEquiv_step, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    exact x.property n⟩
  left_inv x := Subtype.ext (funext fun n => (levelEquiv X l k n).symm_apply_apply (x.val n))
  right_inv x := Subtype.ext (funext fun n => (levelEquiv X l k n).apply_symm_apply (x.val n))
  map_add' x y := Subtype.ext (funext fun n => (levelEquiv X l k n).map_add (x.val n) (y.val n))

end

end ManuscriptAudit.FullEtaleCyclicHOneLimit

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.FullEtaleCyclicHOneLimit.rootsEquiv
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
