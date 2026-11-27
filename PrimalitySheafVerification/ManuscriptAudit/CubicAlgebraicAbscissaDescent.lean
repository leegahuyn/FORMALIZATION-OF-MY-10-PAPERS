import Lean.Util.CollectAxioms
import Mathlib.FieldTheory.IsAlgClosed.Basic
import PrimalitySheafVerification.ManuscriptAudit.CubicNativePointBaseChange

/-! An actual point with algebraic abscissa descends to an algebraically closed coefficient field. -/

namespace ManuscriptAudit.CubicAlgebraicAbscissaDescent

open Polynomial WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate
open CubicNonsplitThreeAdicTrace CubicNativePointBaseChange

noncomputable section

variable {K L M : Type*} [Field K] [Field L] [IsAlgClosed L] [Field M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [DecidableEq L] [DecidableEq M]

private theorem algebraic_scalar {x : M} (hx : IsAlgebraic L x) :
    ∃ r : L, algebraMap L M r = x := by
  have hp := hx.isIntegral
  have hd := IsAlgClosed.degree_eq_one_of_irreducible L (minpoly.irreducible hp)
  have hl : (minpoly L x).leadingCoeff = 1 := minpoly.monic hp
  have h := minpoly.aeval L x
  rw [eq_X_add_C_of_degree_eq_one hd, hl, C_1, one_mul, aeval_add, aeval_X, aeval_C,
    add_eq_zero_iff_eq_neg] at h
  exact ⟨-((minpoly L x).coeff 0), (map_neg (algebraMap L M) _).trans h.symm⟩

/-- If an affine point's abscissa in M is algebraic over the algebraically closed L,
then the actual point is in the image of base change from L. -/
theorem in_range_of_isAlgebraic (A : K) (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (hA : A ≠ 0) {x y : M} (hP : (Curve (algebraMap K M A)).Nonsingular x y)
    (hx : IsAlgebraic L x) :
    (Affine.Point.some x y hP : GeometricPoints K M A) ∈
      Set.range (pointsMap A (IsScalarTower.toAlgHom K L M)) := by
  let f := IsScalarTower.toAlgHom K L M
  have h₂L : (2 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K L)).mpr h₂
  have h₃L : (3 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K L)).mpr h₃
  have hΔL := CubicThreeTorsionCard.shortCubic_discriminant_ne_zero h₂L h₃L
    ((map_ne_zero (algebraMap K L)).mpr hA)
  have h₂M : (2 : M) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K M)).mpr h₂
  have h₃M : (3 : M) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K M)).mpr h₃
  have hΔM := CubicThreeTorsionCard.shortCubic_discriminant_ne_zero h₂M h₃M
    ((map_ne_zero (algebraMap K M)).mpr hA)
  obtain ⟨u, hu⟩ := algebraic_scalar hx
  obtain ⟨v, hv⟩ := IsAlgClosed.exists_pow_nat_eq (u ^ 3 + algebraMap K L A)
    (n := 2) (by decide)
  have hF : f u = x := hu
  have hy := (nonsingular_iff hΔM x y).mp hP
  have hSquare : y ^ 2 = (f v) ^ 2 := by
    rw [← map_pow, hv, map_add, map_pow, hF, AlgHom.commutes]
    exact hy
  have hBuild (z : L) (hz : z ^ 2 = u ^ 3 + algebraMap K L A) (he : f z = y) :
      (Affine.Point.some x y hP : GeometricPoints K M A) ∈ Set.range (pointsMap A f) := by
    let hp := (nonsingular_iff hΔL u z).mpr hz
    obtain ⟨h', hMap⟩ := pointsMap_some A f u z hp
    refine ⟨.some u z hp, ?_⟩
    rw [hMap, Affine.Point.some.injEq]
    exact ⟨hF, he⟩
  rcases ordinate_eq_of_two_squares hSquare with he | he
  · exact hBuild v hv he.symm
  · exact hBuild (-v) (by simpa using hv) (by rw [map_neg, ← he])

end

end ManuscriptAudit.CubicAlgebraicAbscissaDescent

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicAlgebraicAbscissaDescent.in_range_of_isAlgebraic
  let ax ← collectAxioms name
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  unless ax.all (allowed.contains ·) do
    throwError m!"{name} unexpected axioms {ax}"
  logInfo m!"{name} uses {ax}"
