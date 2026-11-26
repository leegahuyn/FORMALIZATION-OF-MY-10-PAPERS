import Lean.Util.CollectAxioms
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Dimension.Constructions
import PrimalitySheafVerification.ManuscriptAudit.ArithmeticLineHOne
import PrimalitySheafVerification.ManuscriptAudit.ArithmeticLineModel
import PrimalitySheafVerification.ManuscriptAudit.RationalChartGenus
import PrimalitySheafVerification.ManuscriptAudit.SchemeIsoSmallEtaleCohomology

/-!
# The smooth arithmetic affine line contradicts the printed dimension identity

For the actual fiber over five, the ordinary constant Z/2 H¹ has
dimension one. Its normal coordinate ring is the polynomial ring;
the rational compactification contributes genus zero, the single
component has no dual-graph edge, and there are no singular terms.
-/

namespace ManuscriptAudit.ArithmeticLineDimensionCounterexample

open AlgebraicGeometry CategoryTheory ArithmeticLineModel
open scoped BigOperators

noncomputable section

attribute [local instance] ManuscriptAudit.GeometricSkyscraperCohomology.etaleSiteHasExt

private abbrev F := ZMod 2
private abbrev cyclic := AddCommGrpCat.of F

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

abbrev fiberHOne :=
  Sheaf.H ((constantSheaf fiberFive.smallEtaleTopology AddCommGrpCat.{0}).obj cyclic) 1

/-- The cohomology equivalence on the actual scheme-theoretic fiber. -/
def fiberCyclicHOneEquiv : F ≃+ fiberHOne :=
  ArithmeticLineHOne.affineLineCyclicHOneEquiv.trans
    (SmallEtaleEquivalenceCohomology.schemeIsoCohomologyEquiv fiberFiveIso cyclic 1).symm

def fiberModule : Module F fiberHOne :=
  AddCommGroup.zmodModule fun x => by
    obtain ⟨a, rfl⟩ := fiberCyclicHOneEquiv.surjective x
    have hCast : ((2 : ℕ) : F) = 0 := by decide
    have ha : (2 : ℕ) • a = 0 := by
      rw [← Nat.cast_smul_eq_nsmul (R := F), hCast, zero_smul]
    rw [← map_nsmul, ha, map_zero]

theorem fiber_finrank :
    letI := fiberModule
    Module.finrank F fiberHOne = 1 := by
  letI := fiberModule
  let e : F ≃ₗ[F] fiberHOne :=
    { fiberCyclicHOneEquiv with map_smul' := ZMod.map_smul fiberCyclicHOneEquiv }
  exact e.finrank_eq.symm.trans (CommSemiring.finrank_self _)

private instance singularFintype : Fintype ↥singularPoints where
  elems := ∅
  complete x := by
    let v : Spec (CommRingCat.of (Polynomial Five)) := x.val
    have h := congrArg (fun U : Set (Spec (CommRingCat.of (Polynomial Five))) => v ∈ U)
      singularPoints_eq_empty
    exact False.elim (Eq.mp h x.property)

/-- The connected dual graph has one vertex and zero edges. -/
def dualGraphBetti : ℕ :=
  Fintype.card (Fin 0) + 1 - Fintype.card (Fin 1)

theorem dualGraphBetti_eq_zero : dualGraphBetti = 0 := by
  simp [dualGraphBetti]

def singularDeltaSum (δ : ↥singularPoints → ℕ) : ℕ := ∑ x, δ x

theorem singularDeltaSum_eq_zero (δ : ↥singularPoints → ℕ) : singularDeltaSum δ = 0 :=
  rfl

def printedRightSide (δ : ↥singularPoints → ℕ) : ℕ :=
  2 * RationalChartGenus.genus Five + dualGraphBetti + singularDeltaSum δ

theorem printedRightSide_eq_zero (δ : ↥singularPoints → ℕ) : printedRightSide δ = 0 := by
  rw [printedRightSide, RationalChartGenus.genus_eq_zero, dualGraphBetti_eq_zero,
    singularDeltaSum_eq_zero] <;> rfl

/-- Physical p. 199, §6.3, fails for the smooth fiber of A¹ over five. -/
theorem printed_dimension_ne (δ : ↥singularPoints → ℕ) :
    letI := fiberModule
    Module.finrank F fiberHOne ≠ printedRightSide δ := by
  letI := fiberModule
  rw [fiber_finrank, printedRightSide_eq_zero]
  exact Nat.one_ne_zero

end

end ManuscriptAudit.ArithmeticLineDimensionCounterexample

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in
    [``ManuscriptAudit.ArithmeticLineDimensionCounterexample.fiberCyclicHOneEquiv,
      ``ManuscriptAudit.ArithmeticLineDimensionCounterexample.fiber_finrank,
      ``ManuscriptAudit.ArithmeticLineDimensionCounterexample.printedRightSide_eq_zero,
      ``ManuscriptAudit.ArithmeticLineDimensionCounterexample.printed_dimension_ne] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter (fun axiomName => !allowed.contains axiomName)
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
