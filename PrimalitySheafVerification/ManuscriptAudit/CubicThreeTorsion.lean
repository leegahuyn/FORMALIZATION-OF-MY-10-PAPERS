import Lean.Util.CollectAxioms
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.CubicTwoTorsion

/-! Actual geometric three-torsion on the short Weierstrass cubic y²=x³+A. -/

namespace ManuscriptAudit.CubicThreeTorsion

open WeierstrassCurve FiniteFieldPointCount CubicTwoTorsion

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K]

abbrev ThreeTorsion (A : K) := {P : (CubicAffine (0 : K) A).Point // 3 • P = 0}

abbrev FlexAbscissas (A : K) := {x : K // x * (x ^ 3 + 4 * A) = 0}

abbrev Ordinates (A : K) (x : FlexAbscissas A) := {y : K // y ^ 2 = x.val ^ 3 + A}

abbrev FlexCoordinates (A : K) := Σ x : FlexAbscissas A, Ordinates A x

private theorem equation_iff {A : K} (hΔ : (shortCubic (0 : K) A).Δ ≠ 0) (x y : K) :
    (CubicAffine (0 : K) A).Nonsingular x y ↔ y ^ 2 = x ^ 3 + A := by
  rw [← Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ, Affine.equation_iff]
  simp [CubicAffine, shortCubic]

private theorem three_nsmul_eq_zero_iff {G : Type*} [AddCommGroup G] (P : G) :
    3 • P = 0 ↔ P + P = -P := by
  rw [show (3 : ℕ) = 2 + 1 by decide, add_nsmul, one_nsmul, two_nsmul]
  constructor
  · intro h
    calc
      P + P = (P + P) + (P + -P) := by rw [add_neg_cancel, add_zero]
      _ = ((P + P) + P) + -P := (add_assoc _ _ _).symm
      _ = -P := by rw [h, zero_add]
  · intro h
    rw [h, neg_add_cancel]

/-- The affine point is three-torsion exactly when its tangent meets it with multiplicity three. -/
theorem three_nsmul_affine_some_iff {A x y : K}
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hΔ : (shortCubic (0 : K) A).Δ ≠ 0)
    (h : (CubicAffine (0 : K) A).Nonsingular x y) :
    (3 • (Affine.Point.some x y h : (CubicAffine (0 : K) A).Point) = 0) ↔
      y ≠ 0 ∧ x * (x ^ 3 + 4 * A) = 0 := by
  let W := CubicAffine (0 : K) A
  by_cases hy : y = 0
  · have htwo := (two_nsmul_affine_some_iff h₂ h).mpr hy
    have hnot : ¬3 • (Affine.Point.some x y h : W.Point) = 0 := by
      intro hp
      rw [show (3 : ℕ) = 2 + 1 by decide, add_nsmul, htwo, zero_add, one_nsmul] at hp
      exact Affine.Point.some_ne_zero h hp
    simp [hy, hnot]
  · have hnegY (a b : K) : W.negY a b = -b := by
      simp [W, CubicAffine, shortCubic, Affine.negY]
    have hd : (2 : K) * y ≠ 0 := mul_ne_zero h₂ hy
    have hY : y ≠ W.negY x y := by
      rw [hnegY]
      intro he
      apply hd
      calc
        _ = y + y := two_mul y
        _ = (-y) + y := congrArg (fun z => z + y) he
        _ = 0 := neg_add_cancel y
    let ell := W.slope x x y y
    have hell : ell = (3 * x ^ 2) / (2 * y) := by
      change W.slope x x y y = _
      rw [Affine.slope_of_Y_ne rfl hY, hnegY, sub_neg_eq_add, ← two_mul]
      simp [W, CubicAffine, shortCubic]
    have hmul : ell * ((2 : K) * y) = 3 * x ^ 2 := by
      rw [hell, div_mul_cancel₀ _ hd]
    have hEqu := (equation_iff hΔ x y).mp h
    have hxCoord : W.addX x x ell = ell ^ 2 - x - x := by
      simp [W, CubicAffine, shortCubic, Affine.addX]
    have key : (ell ^ 2 - x - x - x) * ((2 : K) * y) ^ 2 =
        -(3 : K) * (x * (x ^ 3 + 4 * A)) := by
      calc
        _ = (ell * ((2 : K) * y)) ^ 2 - 12 * x * y ^ 2 := by ring
        _ = _ := by rw [hmul, hEqu]; ring
    have hxIff : W.addX x x ell = x ↔ x * (x ^ 3 + 4 * A) = 0 := by
      rw [← sub_eq_zero, hxCoord]
      constructor
      · intro hh
        have hh' := congrArg (fun a : K => a * ((2 : K) * y) ^ 2) hh
        rw [key, zero_mul] at hh'
        exact (mul_eq_zero.mp hh').resolve_left (neg_ne_zero.mpr h₃)
      · intro hh
        have hh' : (ell ^ 2 - x - x - x) * ((2 : K) * y) ^ 2 = 0 :=
          key.trans (by rw [hh, mul_zero])
        exact (mul_eq_zero.mp hh').resolve_right (pow_ne_zero _ hd)
    rw [three_nsmul_eq_zero_iff, Affine.Point.add_of_Y_ne hY, Affine.Point.neg_some]
    constructor
    · intro hp
      exact ⟨hy, hxIff.mp (Affine.Point.some.inj hp).1⟩
    · rintro ⟨_, hx⟩
      have hx' := hxIff.mpr hx
      have hy' : W.addY x x y ell = W.negY x y := by
        simp only [Affine.addY, Affine.negAddY, hx', sub_self, mul_zero, zero_add]
      simpa only [Affine.Point.some.injEq] using And.intro hx' hy'

/-- The ordinate square cannot vanish at a flex abscissa on the good cubic. -/
theorem ordinate_square_ne_zero {A : K} (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0)
    (x : FlexAbscissas A) : x.val ^ 3 + A ≠ 0 := by
  rcases mul_eq_zero.mp x.property with hx | hx
  · simpa [hx] using hA
  · intro hz
    apply mul_ne_zero h₃ hA
    calc
      (3 : K) * A = (x.val ^ 3 + 4 * A) - (x.val ^ 3 + A) := by ring
      _ = 0 := by rw [hx, hz, sub_self]

/-- The point at infinity and the affine flexes give every actual three-torsion point. -/
def affineThreeTorsionEquiv {A : K} (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (hA : A ≠ 0) (hΔ : (shortCubic (0 : K) A).Δ ≠ 0) :
    ThreeTorsion A ≃ Option (FlexCoordinates A) where
  toFun
    | ⟨.zero, _⟩ => none
    | ⟨.some x y h, hP⟩ => by
      have hx := ((three_nsmul_affine_some_iff h₂ h₃ hΔ h).mp hP).2
      exact some ⟨⟨x, hx⟩, ⟨y, (equation_iff hΔ x y).mp h⟩⟩
  invFun
    | none => ⟨0, nsmul_zero _⟩
    | some ⟨x, y⟩ => by
      have hy : y.val ≠ 0 := by
        intro hy
        exact ordinate_square_ne_zero h₃ hA x (by simpa [hy] using y.property.symm)
      have h := (equation_iff hΔ x.val y.val).mpr y.property
      exact ⟨.some x.val y.val h, (three_nsmul_affine_some_iff h₂ h₃ hΔ h).mpr ⟨hy, x.property⟩⟩
  left_inv := by
    rintro ⟨P, hP⟩
    cases P <;> rfl
  right_inv := by
    rintro (_ | ⟨⟨x, hx⟩, ⟨y, hy⟩⟩) <;> rfl

def projectiveThreeTorsionEquiv {A : K} (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (hA : A ≠ 0) (hΔ : (shortCubic (0 : K) A).Δ ≠ 0) :
    {P : (shortCubic (0 : K) A).toProjective.Point // 3 • P = 0} ≃ Option (FlexCoordinates A) := by
  let e := Projective.Point.toAffineAddEquiv (W := (shortCubic (0 : K) A).toProjective)
  let er : {P : (shortCubic (0 : K) A).toProjective.Point // 3 • P = 0} ≃ ThreeTorsion A :=
    { toFun := fun P => ⟨e P, by rw [← map_nsmul, P.property, map_zero]⟩
      invFun := fun Q => ⟨e.symm Q, by rw [← map_nsmul, Q.property, map_zero]⟩
      left_inv := fun P => Subtype.ext (e.symm_apply_apply P)
      right_inv := fun Q => Subtype.ext (e.apply_symm_apply Q) }
  exact er.trans (affineThreeTorsionEquiv h₂ h₃ hA hΔ)

end
end ManuscriptAudit.CubicThreeTorsion

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicThreeTorsion.three_nsmul_affine_some_iff,
      ``ManuscriptAudit.CubicThreeTorsion.ordinate_square_ne_zero,
      ``ManuscriptAudit.CubicThreeTorsion.affineThreeTorsionEquiv,
      ``ManuscriptAudit.CubicThreeTorsion.projectiveThreeTorsionEquiv] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
