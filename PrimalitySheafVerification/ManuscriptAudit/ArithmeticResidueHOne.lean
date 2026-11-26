import Lean.Util.CollectAxioms
import Mathlib.Data.ZMod.Basic
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleCuspHOne
import PrimalitySheafVerification.ManuscriptAudit.CuspRootCoefficients
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleCohomologyComparison

/-!
# Arithmetic small étale cohomology at a finite-field point

The underlying one-point space of Spec F₅ does not kill positive-degree
étale cohomology. With constant Z/2 coefficients its actual H¹ is Z/2.
This uses the Kummer sequence and the two square classes of F₅ units.
-/

namespace ManuscriptAudit.ArithmeticResidueHOne

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open KummerAffineCohomology SmallEtaleCohomologyComparison

noncomputable section

private abbrev K := ZMod 5
private abbrev R := CommRingCat.of K
private abbrev cyclic := AddCommGrpCat.of (ZMod 2)

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : NeZero ((2 : ℕ) : K) := ⟨by decide⟩

private theorem primitiveNegOne : IsPrimitiveRoot (-1 : K) 2 :=
  IsPrimitiveRoot.neg_one 5 (by decide)

local instance : HasEnoughRootsOfUnity K 2 where
  prim := ⟨-1, primitiveNegOne⟩
  cyc := rootsOfUnity.isCyclic K 2

attribute [local instance] KummerCohomologySequence.affineSiteHasExt fullSiteHasExt

private abbrev J := Scheme.AffineEtale.topology (Spec R)
private abbrev HR :=
  Sheaf.H ((constantSheaf J AddCommGrpCat.{0}).obj
    (KummerConstantCoefficients.coefficientGroup K 2)) 1

private theorem two_isUnit : IsUnit ((2 : ℕ) : R) :=
  isUnit_iff_ne_zero.mpr (NeZero.ne ((2 : ℕ) : K))

private def boundary : Additive Kˣ →+ HR :=
  unitBoundary (K := K) R 2 (by decide) two_isUnit

private def twoUnit : Kˣ := Units.mk0 2 (by decide)

private theorem boundary_square_zero (x : Kˣ) :
    boundary (Additive.ofMul (x ^ (2 : ℕ))) = 0 :=
  (unitBoundary_eq_zero_iff (K := K) R 2 (by decide) two_isUnit _).mpr ⟨x, rfl⟩

private theorem boundary_two_nonzero : boundary (Additive.ofMul twoUnit) ≠ 0 := by
  intro h
  obtain ⟨x, hx⟩ := (unitBoundary_eq_zero_iff (K := K) R 2 (by decide) two_isUnit _).mp h
  have hNoSquare : ∀ a : K, a ^ (2 : ℕ) ≠ (2 : K) := by decide
  exact hNoSquare (x : K) (congrArg Units.val hx)

private theorem root_classes (u : HR) :
    u = 0 ∨ u = boundary (Additive.ofMul twoUnit) := by
  obtain ⟨x, rfl⟩ := unitBoundary_surjective_of_unitHOne (K := K) R 2 (by decide)
    two_isUnit (AffineEtaleCuspHOne.unitSheaf_HOne_subsingleton_of_pid K) u
  change boundary x = 0 ∨ boundary x = _
  have hClasses : ∀ a : K, a ≠ 0 →
      (∃ b : K, b ≠ 0 ∧ b ^ (2 : ℕ) = a) ∨
      ∃ b : K, b ≠ 0 ∧ b ^ (2 : ℕ) * 2 = a := by decide
  rcases hClasses (x.toMul : K) x.toMul.ne_zero with ⟨v, hV, hPower⟩ | ⟨v, hV, hPower⟩
  · let y := Units.mk0 v hV
    have hy : y ^ (2 : ℕ) = x.toMul := Units.ext hPower
    left
    rw [show x = Additive.ofMul (y ^ (2 : ℕ)) from Additive.ext hy.symm]
    exact boundary_square_zero y
  · let y := Units.mk0 v hV
    have hy : y ^ (2 : ℕ) * twoUnit = x.toMul := Units.ext hPower
    right
    rw [show x = Additive.ofMul (y ^ (2 : ℕ)) + Additive.ofMul twoUnit
        from Additive.ext hy.symm, map_add, boundary_square_zero, zero_add]

private def cyclicToRoots : ZMod 2 →+ HR := by
  let a := boundary (Additive.ofMul twoUnit)
  let f : ℤ →+ HR :=
    { toFun := fun n => n • a
      map_zero' := zero_zsmul a
      map_add' := fun m n => add_zsmul a m n }
  refine ZMod.lift 2 ⟨f, ?_⟩
  change (2 : ℤ) • a = 0
  calc
    (2 : ℤ) • a = a + a := by simpa using two_zsmul a
    _ = boundary (Additive.ofMul (twoUnit ^ (2 : ℕ))) := by
      rw [pow_two]
      exact (map_add boundary (Additive.ofMul twoUnit) (Additive.ofMul twoUnit)).symm
    _ = 0 := boundary_square_zero twoUnit

private theorem cyclicToRoots_one :
    cyclicToRoots 1 = boundary (Additive.ofMul twoUnit) := by
  rw [show (1 : ZMod 2) = ((1 : ℤ) : ZMod 2) by simp]
  unfold cyclicToRoots
  rw [ZMod.lift_coe] <;> exact one_zsmul _

/-- The actual arithmetic small étale H¹ of the finite-field point is cyclic of order two. -/
def residueCyclicHOneEquiv : ZMod 2 ≃+
    Sheaf.H ((constantSheaf (Spec R).smallEtaleTopology AddCommGrpCat.{0}).obj cyclic) 1 := by
  have hCases : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  let e := AddEquiv.ofBijective cyclicToRoots ⟨by
    intro x y h
    rcases hCases x with rfl | rfl <;> rcases hCases y with rfl | rfl
    · rfl
    · exact False.elim (boundary_two_nonzero (by simpa only [map_zero, cyclicToRoots_one] using h.symm))
    · exact False.elim (boundary_two_nonzero (by simpa only [map_zero, cyclicToRoots_one] using h))
    · rfl,
    by
      intro a
      rcases root_classes a with h | h
      · exact ⟨0, (map_zero cyclicToRoots).trans h.symm⟩
      · exact ⟨1, cyclicToRoots_one.trans h.symm⟩⟩
  let t : Additive (rootsOfUnity 2 K) ≃+ ZMod 2 :=
    (CuspRootCoefficients.rootsOfUnityEquivZModOfPrimitiveRoot primitiveNegOne).toAdditive
  let ti := (constantSheaf J AddCommGrpCat.{0}).mapIso
    (t.toAddCommGrpIso : KummerConstantCoefficients.coefficientGroup K 2 ≅ cyclic)
  exact e.trans (((Sheaf.functorH J 1).mapIso ti).addCommGroupIsoToAddEquiv.trans
    (cohomologyEquiv R cyclic 1))

theorem residueHOne_not_subsingleton :
    ¬ Subsingleton (Sheaf.H ((constantSheaf (Spec R).smallEtaleTopology
      AddCommGrpCat.{0}).obj cyclic) 1) := by
  intro h
  have h01 := residueCyclicHOneEquiv.injective
    (h.elim (residueCyclicHOneEquiv 0) (residueCyclicHOneEquiv 1))
  exact (by decide : (0 : ZMod 2) ≠ 1) h01

end

end ManuscriptAudit.ArithmeticResidueHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.ArithmeticResidueHOne.residueCyclicHOneEquiv,
      ``ManuscriptAudit.ArithmeticResidueHOne.residueHOne_not_subsingleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
