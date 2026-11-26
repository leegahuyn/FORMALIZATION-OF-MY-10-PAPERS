import Lean.Util.CollectAxioms
import Mathlib.Data.ZMod.Basic
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleCuspHOne
import PrimalitySheafVerification.ManuscriptAudit.CuspRootCoefficients
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleCohomologyComparison

/-!
# Arithmetic étale H¹ of the affine line over F₅

A nonsquare scalar unit gives a nonzero class in actual constant
Z/2 étale cohomology. The calculation uses the Kummer sequence
on the affine étale site and transports to the full small site.
-/

namespace ManuscriptAudit.ArithmeticLineHOne

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open KummerAffineCohomology SmallEtaleCohomologyComparison

noncomputable section

private abbrev K := ZMod 5
private abbrev R := CommRingCat.of (Polynomial K)
private abbrev cyclic := AddCommGrpCat.of (ZMod 2)

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : NeZero ((2 : ℕ) : K) := ⟨by decide⟩

private theorem primitiveNegOne : IsPrimitiveRoot (-1 : K) 2 :=
  IsPrimitiveRoot.neg_one 5 (by decide)

local instance : HasEnoughRootsOfUnity K 2 where
  prim := ⟨-1, primitiveNegOne⟩
  cyc := rootsOfUnity.isCyclic K 2

private def twoUnit : (Polynomial K)ˣ :=
  Units.map (Polynomial.C : K →+* Polynomial K).toMonoidHom (Units.mk0 2 (by decide))

/-- The actual unit 2 in F₅[t] is excluded from the image of the squaring map. -/
theorem scalar_two_not_square (x : (Polynomial K)ˣ) : x ^ (2 : ℕ) ≠ twoUnit := by
  intro h
  have hPoly : (x : Polynomial K) ^ (2 : ℕ) = Polynomial.C 2 :=
    congrArg Units.val h
  have hValue := congrArg (Polynomial.evalRingHom (0 : K)) hPoly
  have hNoSquare : ∀ a : K, a ^ (2 : ℕ) ≠ (2 : K) := by decide
  exact hNoSquare ((Polynomial.evalRingHom (0 : K)) (x : Polynomial K)) (by simpa using hValue)

attribute [local instance] KummerCohomologySequence.affineSiteHasExt fullSiteHasExt

/-- The full arithmetic small étale H¹ of the smooth affine line over F₅
with constant Z/2 coefficients is nontrivial. -/
theorem affine_line_Five_cyclic_HOne_nontrivial :
    ¬ Subsingleton (Sheaf.H ((constantSheaf (Spec R).smallEtaleTopology
      AddCommGrpCat.{0}).obj cyclic) 1) := by
  let J := Scheme.AffineEtale.topology (Spec R)
  have hd : IsUnit ((2 : ℕ) : R) := by
    change IsUnit ((2 : ℕ) : Polynomial K)
    have h : IsUnit ((2 : ℕ) : K) := isUnit_iff_ne_zero.mpr (NeZero.ne _)
    simpa only [map_natCast] using h.map (algebraMap K (Polynomial K))
  let a := unitBoundary (K := K) R 2 (by decide) hd (Additive.ofMul twoUnit)
  have ha : a ≠ 0 := by
    intro ha
    obtain ⟨x, hx⟩ := (unitBoundary_eq_zero_iff (K := K) R 2 (by decide) hd
      (Additive.ofMul twoUnit)).mp ha
    exact scalar_two_not_square x hx
  let t : Additive (rootsOfUnity 2 K) ≃+ ZMod 2 :=
    (CuspRootCoefficients.rootsOfUnityEquivZModOfPrimitiveRoot primitiveNegOne).toAdditive
  let ti := (constantSheaf J AddCommGrpCat.{0}).mapIso
    (t.toAddCommGrpIso : KummerConstantCoefficients.coefficientGroup K 2 ≅ cyclic)
  let e := ((Sheaf.functorH J 1).mapIso ti).addCommGroupIsoToAddEquiv.trans
    (cohomologyEquiv R cyclic 1)
  intro h
  exact ha (e.injective (h.elim (e a) (e 0)))

private def scalarUnit (u : Kˣ) : (Polynomial K)ˣ :=
  Units.map (Polynomial.C : K →+* Polynomial K).toMonoidHom u

/-- Each polynomial unit over F₅ is a square or twice a square. -/
theorem polynomial_unit_square_classes (u : (Polynomial K)ˣ) :
    (∃ x : (Polynomial K)ˣ, x ^ (2 : ℕ) = u) ∨
      ∃ x : (Polynomial K)ˣ, x ^ (2 : ℕ) * twoUnit = u := by
  obtain ⟨a, ha, hCast⟩ := Polynomial.isUnit_iff.mp u.isUnit
  have hClasses : ∀ a : K, a ≠ 0 →
      (∃ b : K, b ≠ 0 ∧ b ^ (2 : ℕ) = a) ∨
      ∃ b : K, b ≠ 0 ∧ b ^ (2 : ℕ) * 2 = a := by decide
  rcases hClasses a ha.ne_zero with ⟨b, hb, hPower⟩ | ⟨b, hb, hPower⟩
  · refine Or.inl ⟨scalarUnit (Units.mk0 b hb), Units.ext ?_⟩
    change Polynomial.C b ^ (2 : ℕ) = (u : Polynomial K)
    rw [← map_pow, hPower, hCast]
  · refine Or.inr ⟨scalarUnit (Units.mk0 b hb), Units.ext ?_⟩
    change Polynomial.C b ^ (2 : ℕ) * Polynomial.C 2 = (u : Polynomial K)
    rw [← map_pow, ← map_mul, hPower, hCast]

private theorem two_isUnit : IsUnit ((2 : ℕ) : R) := by
  change IsUnit ((2 : ℕ) : Polynomial K)
  have h : IsUnit ((2 : ℕ) : K) := isUnit_iff_ne_zero.mpr (NeZero.ne _)
  simpa only [map_natCast] using h.map (algebraMap K (Polynomial K))

private abbrev J := Scheme.AffineEtale.topology (Spec R)
private abbrev HR :=
  Sheaf.H ((constantSheaf J AddCommGrpCat.{0}).obj
    (KummerConstantCoefficients.coefficientGroup K 2)) 1

private def boundary : Additive (Polynomial K)ˣ →+ HR :=
  unitBoundary (K := K) R 2 (by decide) two_isUnit

private theorem boundary_square_zero (x : (Polynomial K)ˣ) :
    boundary (Additive.ofMul (x ^ (2 : ℕ))) = 0 :=
  (unitBoundary_eq_zero_iff (K := K) R 2 (by decide) two_isUnit _).mpr ⟨x, rfl⟩

private theorem boundary_two_nonzero : boundary (Additive.ofMul twoUnit) ≠ 0 := by
  intro h
  obtain ⟨x, hx⟩ := (unitBoundary_eq_zero_iff (K := K) R 2 (by decide) two_isUnit _).mp h
  exact scalar_two_not_square x hx

private theorem root_classes (u : HR) :
    u = 0 ∨ u = boundary (Additive.ofMul twoUnit) := by
  obtain ⟨x, rfl⟩ := unitBoundary_surjective_of_unitHOne (K := K) R 2 (by decide)
    two_isUnit (AffineEtaleCuspHOne.unitSheaf_HOne_subsingleton_of_pid (Polynomial K)) u
  change boundary x = 0 ∨ boundary x = _
  rcases polynomial_unit_square_classes x.toMul with ⟨v, hv⟩ | ⟨v, hv⟩
  · left
    rw [show x = Additive.ofMul (v ^ (2 : ℕ)) from Additive.ext hv.symm]
    exact boundary_square_zero v
  · right
    rw [show x = Additive.ofMul (v ^ (2 : ℕ)) + Additive.ofMul twoUnit from Additive.ext hv.symm,
      map_add, boundary_square_zero, zero_add]

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

/-- Exact arithmetic H¹ of the affine line with constant Z/2 coefficients. -/
def affineLineCyclicHOneEquiv : ZMod 2 ≃+
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

end

end ManuscriptAudit.ArithmeticLineHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
    ``ManuscriptAudit.ArithmeticLineHOne.scalar_two_not_square,
    ``ManuscriptAudit.ArithmeticLineHOne.affine_line_Five_cyclic_HOne_nontrivial,
    ``ManuscriptAudit.ArithmeticLineHOne.polynomial_unit_square_classes,
    ``ManuscriptAudit.ArithmeticLineHOne.affineLineCyclicHOneEquiv] do
    let deps ← collectAxioms name
    let unexpected := deps.filter fun a => !allowed.contains a
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {deps}"
