import Lean.Util.CollectAxioms
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.NormNum
import PrimalitySheafVerification.ManuscriptAudit.ArithmeticLaurentHOne
import PrimalitySheafVerification.ManuscriptAudit.ArithmeticLineHOne
import PrimalitySheafVerification.ManuscriptAudit.CuspSmallEtaleCohomology

/-!
# The signed arithmetic étale H¹ jump over F₅

The affine cusp has one arithmetic order-two H¹ class up to span,
coming from a nonsquare scalar. The punctured cusp has the additional
class of the Laurent coordinate. The two full small étale groups are
therefore one- and two-dimensional over the coefficient field.
-/

namespace ManuscriptAudit.ArithmeticCuspBump

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian

noncomputable section

attribute [local instance] SmallEtaleCohomologyComparison.fullSiteHasExt

private abbrev K := ZMod 5
private abbrev F := ZMod 2
private abbrev cyclic := AddCommGrpCat.of F

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private abbrev cuspRing := CommRingCat.of (CuspPunctured.CuspSubalgebra K)
private abbrev punctureRing :=
  CommRingCat.of (Localization.Away (CuspPunctured.cuspSquare K))

private abbrev cyclicHOne (R : CommRingCat.{0}) :=
  Sheaf.H ((constantSheaf (Spec R).smallEtaleTopology AddCommGrpCat.{0}).obj cyclic) 1

/-- Actual arithmetic H¹ of the unpunctured cusp over F₅ is cyclic of order two. -/
def cuspCyclicHOneEquiv : F ≃+ cyclicHOne cuspRing :=
  ArithmeticLineHOne.affineLineCyclicHOneEquiv.trans
    (CuspSmallEtaleCohomology.normalizationCohomologyEquiv K 5 cyclic 1).symm

private def coefficientModule {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module F M] (e : M ≃+ N) : Module F N :=
  AddCommGroup.zmodModule fun x => by
    obtain ⟨a, rfl⟩ := e.surjective x
    have hCast : ((2 : ℕ) : F) = 0 := by decide
    have ha : (2 : ℕ) • a = 0 := by
      rw [← Nat.cast_smul_eq_nsmul (R := F), hCast, zero_smul]
    rw [← map_nsmul, ha, map_zero]

/-- Coefficient-field structure on the actual arithmetic cusp cohomology. -/
def cuspModule : Module F (cyclicHOne cuspRing) :=
  coefficientModule cuspCyclicHOneEquiv

/-- Coefficient-field structure on the actual arithmetic puncture cohomology. -/
def punctureModule : Module F (cyclicHOne punctureRing) :=
  coefficientModule ArithmeticLaurentHOne.puncturedCuspCyclicHOneEquiv

/-- The two arithmetic dimensions over the coefficient field are 1 and 2. -/
theorem cusp_and_puncture_finranks :
    letI := cuspModule
    letI := punctureModule
    Module.finrank F (cyclicHOne cuspRing) = 1 ∧
      Module.finrank F (cyclicHOne punctureRing) = 2 := by
  letI := cuspModule
  letI := punctureModule
  let e : F ≃ₗ[F] cyclicHOne cuspRing :=
    { cuspCyclicHOneEquiv with map_smul' := ZMod.map_smul cuspCyclicHOneEquiv }
  let f := ArithmeticLaurentHOne.puncturedCuspCyclicHOneEquiv
  let fLinear : (F × F) ≃ₗ[F] cyclicHOne punctureRing :=
    { f with map_smul' := ZMod.map_smul f }
  refine ⟨e.finrank_eq.symm.trans (CommSemiring.finrank_self _), ?_⟩
  rw [← fLinear.finrank_eq, Module.finrank_prod, CommSemiring.finrank_self] <;> norm_num

/-- The literal signed difference on the arithmetic base field is −1. -/
theorem arithmetic_cusp_signed_bump :
    letI := cuspModule
    letI := punctureModule
    (Module.finrank F (cyclicHOne cuspRing) : ℤ) -
      (Module.finrank F (cyclicHOne punctureRing) : ℤ) = -1 := by
  letI := cuspModule
  letI := punctureModule
  obtain ⟨hc, hp⟩ := cusp_and_puncture_finranks
  rw [hc, hp] <;> norm_num

end

end ManuscriptAudit.ArithmeticCuspBump

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.ArithmeticCuspBump.cuspCyclicHOneEquiv,
      ``ManuscriptAudit.ArithmeticCuspBump.cusp_and_puncture_finranks,
      ``ManuscriptAudit.ArithmeticCuspBump.arithmetic_cusp_signed_bump] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
