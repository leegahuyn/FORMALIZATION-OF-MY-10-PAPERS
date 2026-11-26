import Lean.Util.CollectAxioms
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic.NormNum
import PrimalitySheafVerification.ManuscriptAudit.CuspSmallEtaleCohomology

/-!
# The signed geometric étale H¹ jump of the affine cusp

The affine cusp and its puncture have dimensions 0 and 1 over the
prime coefficient field. The dimensions refer to their full small
étale cohomology groups with constant coefficients.
-/

namespace ManuscriptAudit.GeometricCuspBump

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian

noncomputable section

attribute [local instance] SmallEtaleCohomologyComparison.fullSiteHasExt

variable (K : Type) [Field K] [hClosed : IsAlgClosed K]

private abbrev cuspRing := CommRingCat.of (CuspPunctured.CuspSubalgebra K)
private abbrev punctureRing :=
  CommRingCat.of (Localization.Away (CuspPunctured.cuspSquare K))

/-- Constant cyclic H¹ on the full native small étale site of an affine scheme. -/
abbrev cyclicHOne (R : CommRingCat.{0}) (ell : ℕ) :=
  Sheaf.H ((constantSheaf (Spec R).smallEtaleTopology AddCommGrpCat.{0}).obj
    (AddCommGrpCat.of (ZMod ell))) 1

variable (ell : ℕ) [ellPrime : Fact ell.Prime] [ellNonzero : NeZero (ell : K)]
include hClosed ellPrime ellNonzero

/-- The prime coefficient module on the unpunctured cusp's actual H¹. -/
def cuspModule (p : ℕ) [Fact p.Prime] [CharP K p] :
    Module (ZMod ell) (cyclicHOne (cuspRing K) ell) :=
  AddCommGroup.zmodModule fun x =>
    (CuspSmallEtaleCohomology.cusp_cyclic_HOne_subsingleton K p ell).elim _ _

/-- The prime coefficient module on the punctured cusp's actual H¹. -/
def punctureModule : Module (ZMod ell) (cyclicHOne (punctureRing K) ell) :=
  AddCommGroup.zmodModule fun x => by
    let e := SmallEtaleCuspHOne.puncturedCuspCyclicHOneEquiv K ell (Fact.out : ell.Prime).two_le
    obtain ⟨a, rfl⟩ := e.surjective x
    have ha : ell • a = 0 := by simp [nsmul_eq_mul]
    rw [← map_nsmul, ha, map_zero]

/-- The two actual geometric small étale H¹ dimensions are zero and one. -/
theorem cusp_and_puncture_finranks (p : ℕ) [Fact p.Prime] [CharP K p] :
    letI := cuspModule K ell p
    letI := punctureModule K ell
    Module.finrank (ZMod ell) (cyclicHOne (cuspRing K) ell) = 0 ∧
      Module.finrank (ZMod ell) (cyclicHOne (punctureRing K) ell) = 1 := by
  letI := cuspModule K ell p
  letI := punctureModule K ell
  letI := CuspSmallEtaleCohomology.cusp_cyclic_HOne_subsingleton K p ell
  refine ⟨Module.finrank_zero_of_subsingleton, ?_⟩
  let e := SmallEtaleCuspHOne.puncturedCuspCyclicHOneEquiv K ell (Fact.out : ell.Prime).two_le
  let eLinear : ZMod ell ≃ₗ[ZMod ell] cyclicHOne (punctureRing K) ell :=
    { e with map_smul' := ZMod.map_smul e }
  exact eLinear.finrank_eq.symm.trans (CommSemiring.finrank_self _)

/-- The printed signed geometric ordinary H¹ difference of cusp and puncture is −1. -/
theorem geometric_cusp_signed_bump (p : ℕ) [Fact p.Prime] [CharP K p] :
    letI := cuspModule K ell p
    letI := punctureModule K ell
    (Module.finrank (ZMod ell) (cyclicHOne (cuspRing K) ell) : ℤ) -
      (Module.finrank (ZMod ell) (cyclicHOne (punctureRing K) ell) : ℤ) = -1 := by
  letI := cuspModule K ell p
  letI := punctureModule K ell
  obtain ⟨hCusp, hPuncture⟩ := cusp_and_puncture_finranks K ell p
  rw [hCusp, hPuncture] <;> norm_num

end

end ManuscriptAudit.GeometricCuspBump

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.GeometricCuspBump.cusp_and_puncture_finranks,
      ``ManuscriptAudit.GeometricCuspBump.geometric_cusp_signed_bump] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
