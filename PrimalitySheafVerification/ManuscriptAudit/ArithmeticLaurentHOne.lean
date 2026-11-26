import Lean.Util.CollectAxioms
import Mathlib.Algebra.Field.ZMod
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleCuspHOne
import PrimalitySheafVerification.ManuscriptAudit.CuspRootCoefficients
import PrimalitySheafVerification.ManuscriptAudit.LaurentUnitRepresentation
import PrimalitySheafVerification.ManuscriptAudit.LaurentUnits
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleCohomologyComparison

/-!
# Arithmetic étale H¹ of the Laurent line over F₅

The two generators of actual constant Z/2 cohomology are the Kummer
classes of the nonsquare scalar 2 and the Laurent coordinate. The
calculation also applies to the actual coordinate ring of the punctured cusp.
-/

namespace ManuscriptAudit.ArithmeticLaurentHOne

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian LaurentPolynomial
open KummerAffineCohomology SmallEtaleCohomologyComparison

noncomputable section

attribute [local instance] KummerCohomologySequence.affineSiteHasExt fullSiteHasExt

private abbrev K := ZMod 5
private abbrev cyclic := AddCommGrpCat.of (ZMod 2)

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : NeZero ((2 : ℕ) : K) := ⟨by decide⟩

private theorem primitiveNegOne : IsPrimitiveRoot (-1 : K) 2 :=
  IsPrimitiveRoot.neg_one 5 (by decide)

local instance : HasEnoughRootsOfUnity K 2 where
  prim := ⟨-1, primitiveNegOne⟩
  cyc := rootsOfUnity.isCyclic K 2

private def twoK : Kˣ := Units.mk0 (2 : K) (by decide)

private theorem scalar_square_classes (u : Kˣ) :
    (∃ v : Kˣ, v ^ (2 : ℕ) = u) ∨ ∃ v : Kˣ, v ^ (2 : ℕ) * twoK = u := by
  have h : ∀ a : K, a ≠ 0 →
      (∃ b : K, b ≠ 0 ∧ b ^ (2 : ℕ) = a) ∨
      ∃ b : K, b ≠ 0 ∧ b ^ (2 : ℕ) * 2 = a := by decide
  rcases h (u : K) u.ne_zero with ⟨b, hb, hPower⟩ | ⟨b, hb, hPower⟩
  · exact Or.inl ⟨Units.mk0 b hb, Units.ext hPower⟩
  · exact Or.inr ⟨Units.mk0 b hb, Units.ext hPower⟩

private abbrev evalAtOne : LaurentPolynomial K →ₐ[K] K :=
  (LaurentUnitRepresentation.laurentAlgHomEquivUnits K K).symm (1 : Kˣ)

private theorem evalAtOne_T_one : evalAtOne (T 1) = 1 := by
  simpa only [evalAtOne, Equiv.apply_symm_apply, Units.val_one] using
    (LaurentUnitRepresentation.laurentAlgHomEquivUnits_val K K evalAtOne).symm

section Coordinates

variable (R : Type) [CommRing R] [Algebra K R]

private abbrev ring := CommRingCat.of R
private abbrev site := Scheme.AffineEtale.topology (Spec (ring R))
private abbrev HR := Sheaf.H ((constantSheaf (site R) AddCommGrpCat.{0}).obj
  (KummerConstantCoefficients.coefficientGroup K 2)) 1

private theorem two_isUnit : IsUnit ((2 : ℕ) : ring R) := by
  change IsUnit ((2 : ℕ) : R)
  have h : IsUnit ((2 : ℕ) : K) := isUnit_iff_ne_zero.mpr (NeZero.ne _)
  simpa only [map_natCast] using h.map (algebraMap K R)

private def boundary : Additive Rˣ →+ HR R :=
  unitBoundary (K := K) (ring R) 2 (by decide) (two_isUnit R)

private theorem boundary_eq_zero (u : Rˣ) :
    boundary R (Additive.ofMul u) = 0 ↔ ∃ v : Rˣ, v ^ (2 : ℕ) = u :=
  unitBoundary_eq_zero_iff (K := K) (ring R) 2 (by decide) (two_isUnit R) _

private theorem boundary_square_zero (u : Rˣ) :
    boundary R (Additive.ofMul (u ^ (2 : ℕ))) = 0 :=
  (boundary_eq_zero R _).mpr ⟨u, rfl⟩

private abbrev scalarUnit : Kˣ →* Rˣ :=
  Units.map (algebraMap K R).toMonoidHom

private def exponentUnit (e : R ≃ₐ[K] LaurentPolynomial K) : ℤ →+ Additive Rˣ where
  toFun n := Additive.ofMul
    (Units.map e.symm.toRingHom.toMonoidHom (unitOfInvertible (T n : LaurentPolynomial K)))
  map_zero' := by
    apply Additive.ext
    apply Units.ext
    change e.symm (T 0) = 1
    simp
  map_add' m n := by
    apply Additive.ext
    apply Units.ext
    change e.symm (T (m + n)) = e.symm (T m) * e.symm (T n)
    rw [T_add, map_mul]

variable (e : R ≃ₐ[K] LaurentPolynomial K)

private theorem unit_factorization (u : Additive Rˣ) :
    ∃ (c : Kˣ) (n : ℤ), Additive.ofMul (scalarUnit R c) + exponentUnit R e n = u := by
  let uL : (LaurentPolynomial K)ˣ := Units.map e.toRingHom.toMonoidHom u.toMul
  obtain ⟨c, n, hc, hu⟩ := (LaurentUnits.laurent_isUnit_iff_monomial K _).mp uL.isUnit
  refine ⟨Units.mk0 c hc.ne_zero, n, Additive.ext (Units.ext (e.injective ?_))⟩
  change e ((algebraMap K R c) * e.symm (T n)) = e (u.toMul : R)
  rw [map_mul, AlgEquiv.apply_symm_apply, e.commutes]
  exact hu.symm

private abbrev evalR : R →ₐ[K] K := evalAtOne.comp e.toAlgHom

private theorem evalR_scalar (a : Kˣ) :
    evalR R e (scalarUnit R a : R) = (a : K) := by
  change evalR R e (algebraMap K R (a : K)) = (a : K)
  rw [(evalR R e).commutes, Algebra.algebraMap_self_apply]

private theorem evalR_coordinate :
    evalR R e ((exponentUnit R e 1).toMul : R) = 1 := by
  change evalAtOne (e (e.symm (T 1))) = 1
  rw [AlgEquiv.apply_symm_apply]
  exact evalAtOne_T_one

private theorem boundary_nonsquare_scalar (u : Rˣ) (hu : evalR R e (u : R) = 2) :
    boundary R (Additive.ofMul u) ≠ 0 := by
  intro h
  obtain ⟨v, hv⟩ := (boundary_eq_zero R u).mp h
  have hVal := congrArg (fun w : Rˣ => evalR R e (w : R)) hv
  change evalR R e ((v : R) ^ (2 : ℕ)) = evalR R e (u : R) at hVal
  rw [map_pow, hu] at hVal
  exact (show ∀ j : K, j ^ (2 : ℕ) ≠ (2 : K) by decide) _ hVal

private theorem boundary_coordinate_nonzero : boundary R (exponentUnit R e 1) ≠ 0 := by
  intro h
  obtain ⟨v, hv⟩ := (boundary_eq_zero R (exponentUnit R e 1).toMul).mp h
  have hVal := congrArg (fun w : Rˣ => e (w : R)) hv
  change e ((v : R) ^ (2 : ℕ)) = e (e.symm (T 1)) at hVal
  rw [map_pow, AlgEquiv.apply_symm_apply] at hVal
  exact LaurentUnits.laurent_T_one_not_unit_pow K (by decide : 2 ≤ 2)
    (Units.map e.toRingHom.toMonoidHom v) hVal

private def cyclicClass (u : Rˣ) : ZMod 2 →+ HR R := by
  let a := boundary R (Additive.ofMul u)
  let f : ℤ →+ HR R :=
    { toFun := fun n => n • a
      map_zero' := zero_zsmul a
      map_add' := fun m n => add_zsmul a m n }
  refine ZMod.lift 2 ⟨f, ?_⟩
  change (2 : ℤ) • a = 0
  calc
    (2 : ℤ) • a = a + a := by simpa using two_zsmul a
    _ = boundary R (Additive.ofMul (u ^ (2 : ℕ))) := by
      rw [pow_two]
      exact (map_add (boundary R) (Additive.ofMul u) (Additive.ofMul u)).symm
    _ = 0 := boundary_square_zero R u

private theorem cyclicClass_intCast (u : Rˣ) (n : ℤ) :
    cyclicClass R u (n : ZMod 2) = n • boundary R (Additive.ofMul u) := by
  unfold cyclicClass
  rw [ZMod.lift_coe]

private theorem cyclicClass_one (u : Rˣ) :
    cyclicClass R u 1 = boundary R (Additive.ofMul u) := by
  simpa only [Int.cast_one, one_zsmul] using cyclicClass_intCast R u 1

private abbrev scalarClass := cyclicClass R (scalarUnit R twoK)
private abbrev coordinateClass := cyclicClass R (exponentUnit R e 1).toMul

private theorem coordinateClass_intCast (n : ℤ) :
    coordinateClass R e (n : ZMod 2) = boundary R (exponentUnit R e n) := by
  rw [cyclicClass_intCast]
  change n • boundary R (exponentUnit R e 1) = _
  let h := (boundary R).comp (exponentUnit R e)
  change n • h 1 = h n
  rw [← map_zsmul, zsmul_one]

private theorem scalarClass_covers (a : Kˣ) :
    ∃ j : ZMod 2, scalarClass R j = boundary R (Additive.ofMul (scalarUnit R a)) := by
  rcases scalar_square_classes a with ⟨v, hv⟩ | ⟨v, hv⟩
  · refine ⟨0, ?_⟩
    rw [map_zero, ← hv, map_pow, boundary_square_zero]
  · refine ⟨1, ?_⟩
    rw [cyclicClass_one, ← hv, map_mul, map_pow]
    change boundary R (Additive.ofMul (scalarUnit R twoK)) =
      boundary R (Additive.ofMul ((scalarUnit R v) ^ (2 : ℕ)) +
        Additive.ofMul (scalarUnit R twoK))
    rw [map_add, boundary_square_zero, zero_add]

private def classes : (ZMod 2 × ZMod 2) →+ HR R where
  toFun j := scalarClass R j.1 + coordinateClass R e j.2
  map_zero' := by simp
  map_add' x y := by
    change scalarClass R (x.1 + y.1) + coordinateClass R e (x.2 + y.2) =
      (scalarClass R x.1 + coordinateClass R e x.2) +
        (scalarClass R y.1 + coordinateClass R e y.2)
    rw [map_add, map_add]
    ac_rfl

private theorem classes_ker (j : ZMod 2 × ZMod 2) (hj : classes R e j = 0) : j = 0 := by
  let t := scalarUnit R twoK
  let q := (exponentUnit R e 1).toMul
  have ht : boundary R (Additive.ofMul t) ≠ 0 :=
    boundary_nonsquare_scalar R e t (evalR_scalar R e twoK)
  have hq : boundary R (Additive.ofMul q) ≠ 0 := boundary_coordinate_nonzero R e
  have hEval : evalR R e ((t * q : Rˣ) : R) = 2 := by
    change evalR R e ((t : R) * (q : R)) = 2
    rw [map_mul, evalR_scalar, evalR_coordinate, mul_one]
    rfl
  have htq : boundary R (Additive.ofMul t) + boundary R (Additive.ofMul q) ≠ 0 := by
    rw [← map_add]
    exact boundary_nonsquare_scalar R e (t * q) hEval
  obtain ⟨x, y⟩ := j
  have hcases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases hcases x with rfl | rfl <;> rcases hcases y with rfl | rfl
  · rfl
  · exact False.elim (hq (by simpa only [classes, map_zero, zero_add, cyclicClass_one] using hj))
  · exact False.elim (ht (by simpa only [classes, map_zero, add_zero, cyclicClass_one] using hj))
  · exact False.elim (htq (by simpa only [classes, cyclicClass_one] using hj))

private theorem classes_injective : Function.Injective (classes R e) := by
  intro x y h
  apply sub_eq_zero.mp
  apply classes_ker R e
  rw [map_sub, h, sub_self]

private theorem classes_surjective [IsDomain R] [IsPrincipalIdealRing R] :
    Function.Surjective (classes R e) := by
  intro h
  obtain ⟨u, rfl⟩ := unitBoundary_surjective_of_unitHOne (K := K) (ring R) 2
    (by decide) (two_isUnit R) (AffineEtaleCuspHOne.unitSheaf_HOne_subsingleton_of_pid R) h
  obtain ⟨a, n, rfl⟩ := unit_factorization R e u
  obtain ⟨j, hj⟩ := scalarClass_covers R a
  refine ⟨(j, (n : ZMod 2)), ?_⟩
  change scalarClass R j + coordinateClass R e n = boundary R
    (Additive.ofMul (scalarUnit R a) + exponentUnit R e n)
  rw [hj, coordinateClass_intCast, map_add]

/-- The arithmetic cohomology of a ring with Laurent coordinates has the two indicated classes. -/
def cyclicHOneEquiv [IsDomain R] [IsPrincipalIdealRing R] :
    (ZMod 2 × ZMod 2) ≃+
      Sheaf.H ((constantSheaf (Spec (ring R)).smallEtaleTopology AddCommGrpCat.{0}).obj cyclic) 1 := by
  let h := AddEquiv.ofBijective (classes R e) ⟨classes_injective R e, classes_surjective R e⟩
  let t : Additive (rootsOfUnity 2 K) ≃+ ZMod 2 :=
    (CuspRootCoefficients.rootsOfUnityEquivZModOfPrimitiveRoot primitiveNegOne).toAdditive
  let ti := (constantSheaf (site R) AddCommGrpCat.{0}).mapIso
    (t.toAddCommGrpIso : KummerConstantCoefficients.coefficientGroup K 2 ≅ cyclic)
  exact h.trans (((Sheaf.functorH (site R) 1).mapIso ti).addCommGroupIsoToAddEquiv.trans
    (cohomologyEquiv (ring R) cyclic 1))

end Coordinates

private theorem laurent_domain_and_pid :
    IsDomain (LaurentPolynomial K) ∧ IsPrincipalIdealRing (LaurentPolynomial K) := by
  let M := Submonoid.powers (Polynomial.X : Polynomial K)
  have hM : M ≤ (Polynomial K)⁰ := by
    rintro _ ⟨n, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
  refine ⟨IsLocalization.isDomain_of_le_nonZeroDivisors (LaurentPolynomial K) hM, ?_⟩
  refine ⟨fun I => ?_⟩
  rw [← IsLocalization.map_under M (LaurentPolynomial K) I]
  exact Submodule.IsPrincipal.map_ringHom (algebraMap (Polynomial K) (LaurentPolynomial K))
    (inferInstance : (I.under (Polynomial K)).IsPrincipal)

/-- Arithmetic full small étale H¹ of the Laurent line over F₅ with constant Z/2 coefficients. -/
def laurentCyclicHOneEquiv :
    (ZMod 2 × ZMod 2) ≃+ Sheaf.H ((constantSheaf
      (Spec (CommRingCat.of (LaurentPolynomial K))).smallEtaleTopology AddCommGrpCat.{0}).obj cyclic) 1 :=
  letI := laurent_domain_and_pid.1
  letI := laurent_domain_and_pid.2
  cyclicHOneEquiv (LaurentPolynomial K) (AlgEquiv.refl : LaurentPolynomial K ≃ₐ[K] LaurentPolynomial K)

private abbrev punctured := Localization.Away (CuspPunctured.cuspSquare K)

/-- Arithmetic full small étale H¹ of the actual punctured cusp with constant Z/2 coefficients. -/
def puncturedCuspCyclicHOneEquiv :
    (ZMod 2 × ZMod 2) ≃+ Sheaf.H ((constantSheaf
      (Spec (CommRingCat.of punctured)).smallEtaleTopology AddCommGrpCat.{0}).obj cyclic) 1 :=
  letI := laurent_domain_and_pid.1
  letI := laurent_domain_and_pid.2
  let e := CuspPunctured.paper2_cusp_punctured_coordinate_equiv K
  letI : IsDomain punctured := MulEquiv.isDomain (LaurentPolynomial K) e.toRingEquiv.toMulEquiv
  letI : IsPrincipalIdealRing punctured :=
    IsPrincipalIdealRing.of_surjective e.symm.toRingHom e.symm.surjective
  cyclicHOneEquiv punctured e

end

end ManuscriptAudit.ArithmeticLaurentHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.ArithmeticLaurentHOne.cyclicHOneEquiv,
      ``ManuscriptAudit.ArithmeticLaurentHOne.laurentCyclicHOneEquiv,
      ``ManuscriptAudit.ArithmeticLaurentHOne.puncturedCuspCyclicHOneEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
