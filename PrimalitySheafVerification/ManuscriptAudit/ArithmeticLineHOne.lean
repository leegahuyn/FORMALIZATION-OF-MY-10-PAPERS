import Lean.Util.CollectAxioms
import Mathlib.Data.ZMod.Basic
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
local instance : NeZero (2 : K) := ⟨by decide⟩

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
  have hd : IsUnit (2 : R) := by
    have h : IsUnit (2 : K) := isUnit_iff_ne_zero.mpr (NeZero.ne _)
    simpa using h.map (algebraMap K (Polynomial K))
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

end

end ManuscriptAudit.ArithmeticLineHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
    ``ManuscriptAudit.ArithmeticLineHOne.scalar_two_not_square,
    ``ManuscriptAudit.ArithmeticLineHOne.affine_line_Five_cyclic_HOne_nontrivial] do
    let deps ← collectAxioms name
    let unexpected := deps.filter fun a => !allowed.contains a
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {deps}"
