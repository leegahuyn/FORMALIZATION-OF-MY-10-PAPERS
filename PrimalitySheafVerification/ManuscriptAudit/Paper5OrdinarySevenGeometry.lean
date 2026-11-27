import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinarySeven

/-!
# The geometric seven-torsion coordinates of the ordinary fiber

The coordinate symmetry \(\varphi(x,y)=(2x,y)\) of the actual curve
\(y^2=x^3+5\) in characteristic 7 is additive.  Horizontal chords give
\(\varphi+\varphi^2=-1\), hence
\((2-\varphi)(2-\varphi^2)=[7]\).
The first factor has trivial kernel. Doubling on the second kernel
then gives the three possible nonzero seven-torsion abscissas.
-/

namespace ManuscriptAudit.Paper5OrdinarySevenGeometry

open WeierstrassCurve ManuscriptAudit.Paper5OrdinarySeven

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable (F : Type*) [Field F] [CharP F 7] [DecidableEq F]

private abbrev W := (ordinaryCurve F).toAffine

private theorem two_cube : (2 : F) ^ 3 = 1 := by
  linear_combination seven_zero F

private theorem two_ne_zero : (2 : F) ≠ 0 := by
  intro h
  apply (one_ne_zero : (1 : F) ≠ 0)
  linear_combination 4 * h - seven_zero F

private theorem five_ne_zero : (5 : F) ≠ 0 := by
  intro h
  apply (one_ne_zero : (1 : F) ≠ 0)
  linear_combination 3 * h - 2 * seven_zero F

theorem negY_eq (x y : F) : (W F).negY x y = -y := by
  simp [Affine.negY, ordinaryCurve]

theorem addX_eq (x₁ x₂ l : F) : (W F).addX x₁ x₂ l = l ^ 2 - x₁ - x₂ := by
  simp [Affine.addX, ordinaryCurve]

theorem addY_eq (x₁ x₂ y l : F) :
    (W F).addY x₁ x₂ y l = -(l * ((W F).addX x₁ x₂ l - x₁) + y) := by
  simp only [Affine.addY, negY_eq, Affine.negAddY]

private theorem y_ne_neg_y {y : F} (hy : y ≠ 0) : y ≠ -y := by
  intro h
  apply hy
  apply (mul_eq_zero.mp (show (2 : F) * y = 0 by linear_combination h)).resolve_left
  exact two_ne_zero F

theorem tangent_slope (x y : F) (h : y ≠ -y) :
    (W F).slope x x y y = 3 * x ^ 2 / (2 * y) := by
  have hne : y ≠ (W F).negY x y := by simpa only [negY_eq] using h
  rw [Affine.slope_of_Y_ne rfl hne]
  have hd : y - -y = 2 * y := by ring
  simp [ordinaryCurve, negY_eq, hd]

private theorem scaledSlope (x₁ x₂ y₁ y₂ : F) :
    (W F).slope (2 * x₁) (2 * x₂) y₁ y₂ =
      (2 : F) ^ 2 * (W F).slope x₁ x₂ y₁ y₂ := by
  by_cases hx : x₁ = x₂
  · subst x₂
    by_cases hy : y₁ = -y₂
    · have h₁ : y₁ = (W F).negY x₁ y₂ := by simpa only [negY_eq] using hy
      have h₂ : y₁ = (W F).negY (2 * x₁) y₂ := by simpa only [negY_eq] using hy
      simp only [Affine.slope_of_Y_eq rfl h₂, Affine.slope_of_Y_eq rfl h₁, mul_zero]
    · have h₁ : y₁ ≠ (W F).negY x₁ y₂ := by simpa only [negY_eq] using hy
      have h₂ : y₁ ≠ (W F).negY (2 * x₁) y₂ := by simpa only [negY_eq] using hy
      rw [Affine.slope_of_Y_ne rfl h₂, Affine.slope_of_Y_ne rfl h₁]
      simp only [negY_eq]
      simp only [W, ordinaryCurve, WeierstrassCurve.toAffine, mul_zero, zero_mul,
        add_zero, sub_zero, div_eq_mul_inv]
      ring
  · have hx' : (2 : F) * x₁ ≠ 2 * x₂ := fun h => hx (mul_left_cancel₀ (two_ne_zero F) h)
    have hd : (2 : F) * x₁ - 2 * x₂ = 2 * (x₁ - x₂) := by ring
    have hi : (2 : F)⁻¹ = (2 : F) ^ 2 := by
      apply inv_eq_of_mul_eq_one_right
      calc
        (2 : F) * 2 ^ 2 = 2 ^ 3 := by ring
        _ = 1 := two_cube F
    rw [Affine.slope_of_X_ne hx', Affine.slope_of_X_ne hx, hd]
    simp only [div_eq_mul_inv, mul_inv_rev, hi]
    ring

private theorem scaledAddX (x₁ x₂ l : F) :
    (W F).addX (2 * x₁) (2 * x₂) ((2 : F) ^ 2 * l) = 2 * (W F).addX x₁ x₂ l := by
  simp only [addX_eq]
  linear_combination (2 * l ^ 2) * two_cube F

private theorem scaledAddY (x₁ x₂ y l : F) :
    (W F).addY (2 * x₁) (2 * x₂) y ((2 : F) ^ 2 * l) = (W F).addY x₁ x₂ y l := by
  simp only [addY_eq, scaledAddX]
  linear_combination (-l * ((W F).addX x₁ x₂ l - x₁)) * two_cube F

theorem scaledNonsingular (x y : F) (h : (W F).Nonsingular x y) :
    (W F).Nonsingular (2 * x) y := by
  apply Affine.equation_iff_nonsingular.mp
  apply (equation_iff F _ _).mpr
  simpa only [mul_pow, two_cube, one_mul] using (equation_iff F x y).mp h.1

private def phiFun : Points F → Points F
  | .zero => .zero
  | .some x y h => .some (2 * x) y (scaledNonsingular F x y h)

private theorem phiFun_some {x y : F} (h : (W F).Nonsingular x y) :
    phiFun F (.some x y h) = .some (2 * x) y (scaledNonsingular F x y h) := rfl

private def phi : Points F →+ Points F where
  toFun := phiFun F
  map_zero' := rfl
  map_add' := by
    intro P Q
    cases P with
    | zero =>
      change phiFun F (0 + Q) = 0 + phiFun F Q
      simp only [zero_add]
    | some x₁ y₁ h₁ =>
      cases Q with
      | zero =>
        change phiFun F ((.some x₁ y₁ h₁ : Points F) + 0) =
          phiFun F (.some x₁ y₁ h₁) + 0
        simp only [add_zero]
      | some x₂ y₂ h₂ =>
        by_cases h : x₁ = x₂ ∧ y₁ = -y₂
        · have h₀ : y₁ = (W F).negY x₂ y₂ := by simpa only [negY_eq] using h.2
          have h₀' : y₁ = (W F).negY (2 * x₂) y₂ := by simpa only [negY_eq] using h.2
          rw [Affine.Point.add_of_Y_eq h.1 h₀, phiFun_some F h₁, phiFun_some F h₂,
            Affine.Point.add_of_Y_eq (congrArg ((2 : F) * ·) h.1) h₀']
          rfl
        · have h₀ : ¬(x₁ = x₂ ∧ y₁ = (W F).negY x₂ y₂) := by
            simpa only [negY_eq] using h
          have h₀' : ¬((2 : F) * x₁ = 2 * x₂ ∧ y₁ = (W F).negY (2 * x₂) y₂) := by
            rintro ⟨hx, hy⟩
            exact h ⟨mul_left_cancel₀ (two_ne_zero F) hx, by simpa only [negY_eq] using hy⟩
          rw [Affine.Point.add_some h₀, phiFun_some F h₁, phiFun_some F h₂,
            Affine.Point.add_some h₀']
          simp only [phiFun_some, Affine.Point.some.injEq, scaledSlope, scaledAddX, scaledAddY,
            and_self]

private theorem phi_app (P : Points F) : phi F P = phiFun F P := rfl

private theorem phi_cubed (P : Points F) : phi F (phi F (phi F P)) = P := by
  cases P with
  | zero => rfl
  | some x y h =>
    simp only [phi_app, phiFun_some, Affine.Point.some.injEq, and_true]
    linear_combination x * seven_zero F

private theorem phi_sum (P : Points F) : phi F P + phi F (phi F P) = -P := by
  cases P with
  | zero =>
    change (0 : Points F) + 0 = -0
    simp
  | some x y h =>
    simp only [phi_app, phiFun_some, Affine.Point.neg_some]
    by_cases hx : x = 0
    · subst x
      simp only [mul_zero]
      have hy : y ≠ 0 := by
        intro hy
        have hE := (equation_iff F 0 y).mp h.1
        apply five_ne_zero F
        simpa [hy] using hE.symm
      have hh : y ≠ -y := y_ne_neg_y F hy
      have hh' : y ≠ (W F).negY 0 y := by simpa only [negY_eq] using hh
      have hs : (W F).slope 0 0 y y = 0 := by
        rw [tangent_slope F 0 y hh]
        simp
      rw [Affine.Point.add_self_of_Y_ne hh']
      simp only [Affine.Point.some.injEq]
      constructor
      · rw [addX_eq, hs]
        simp
      · rw [addY_eq, hs, negY_eq]
        simp
    · have hh : (2 : F) * x ≠ 2 * (2 * x) := by
        intro he
        apply hx
        apply (mul_eq_zero.mp (show (2 : F) * x = 0 by linear_combination -he)).resolve_left
        exact two_ne_zero F
      have hs : (W F).slope (2 * x) (2 * (2 * x)) y y = 0 := by
        rw [Affine.slope_of_X_ne hh, sub_self, zero_div]
      rw [Affine.Point.add_of_X_ne hh]
      simp only [Affine.Point.some.injEq, hs, addY_eq, addX_eq, negY_eq, zero_mul, zero_add,
        and_true]
      linear_combination (-x) * seven_zero F

private theorem doubling_x {x y u v : F} {h : (W F).Nonsingular x y}
    {h' : (W F).Nonsingular u v}
    (hP : (2 : ℕ) • (.some x y h : Points F) = .some u v h') :
    9 * x ^ 4 = (u + 2 * x) * (4 * y ^ 2) := by
  have hy : y ≠ 0 := by
    intro hy
    have hn : y = (W F).negY x y := by rw [negY_eq, hy, neg_zero]
    rw [two_nsmul, Affine.Point.add_self_of_Y_eq hn] at hP
    change Affine.Point.zero = Affine.Point.some u v h' at hP
    cases hP
  have hn := y_ne_neg_y F hy
  have hn' : y ≠ (W F).negY x y := by simpa only [negY_eq] using hn
  rw [two_nsmul, Affine.Point.add_self_of_Y_ne hn'] at hP
  have hxy : (W F).addX x x ((W F).slope x x y y) = u ∧
      (W F).addY x x y ((W F).slope x x y y) = v := by
    simpa only [Affine.Point.some.injEq] using hP
  have he := hxy.1
  rw [addX_eq, tangent_slope F x y hn] at he
  have hs : (3 * x ^ 2 / (2 * y)) ^ 2 = u + 2 * x := by linear_combination he
  rw [div_pow, div_eq_iff (pow_ne_zero _ (mul_ne_zero (two_ne_zero F) hy))] at hs
  linear_combination hs

private theorem two_sub_phi_trivial (P : Points F) (hP : (2 : ℕ) • P = phi F P) :
    P = 0 := by
  cases P with
  | zero => rfl
  | some x y h =>
    by_cases hx : x = 0
    · subst x
      simp only [phi_app, phiFun_some, mul_zero, two_nsmul] at hP
      exact add_right_cancel (hP.trans (zero_add _).symm)
    · simp only [phi_app, phiFun_some] at hP
      have hDouble := doubling_x F hP
      have he := (equation_iff F x y).mp h.1
      have hX : 9 * x ^ 3 = 16 * (x ^ 3 + 5) := by
        apply mul_left_cancel₀ hx
        rw [← he]
        linear_combination hDouble
      exfalso
      apply (one_ne_zero : (1 : F) ≠ 0)
      linear_combination (-5 : F) * hX - (5 * x ^ 3 + 57) * seven_zero F

private theorem factor_two_sub_phi (P : Points F) :
    (2 : ℕ) • ((2 : ℕ) • P - phi F (phi F P)) -
      phi F ((2 : ℕ) • P - phi F (phi F P)) = (7 : ℕ) • P := by
  calc
    _ = (5 : ℕ) • P - (2 : ℕ) • (phi F P + phi F (phi F P)) := by
      rw [map_sub, map_nsmul, phi_cubed]
      abel
    _ = _ := by rw [phi_sum]; abel

private theorem double_eq_phi_squared (P : Points F) (hP : (7 : ℕ) • P = 0) :
    (2 : ℕ) • P = phi F (phi F P) := by
  let Q := (2 : ℕ) • P - phi F (phi F P)
  have hQ : (2 : ℕ) • Q - phi F Q = 0 := by
    change _ = 0
    rw [factor_two_sub_phi, hP]
  exact sub_eq_zero.mp (two_sub_phi_trivial F Q (sub_eq_zero.mp hQ))

/-- The native additive rotation (x,y) ↦ (2x,y). -/
def rotation : AddMonoid.End (Points F) := phi F

theorem rotation_some {x y : F} (h : (W F).Nonsingular x y) :
    rotation F (.some x y h) = .some (2 * x) y (scaledNonsingular F x y h) := rfl

theorem rotation_sum (P : Points F) : rotation F P + rotation F (rotation F P) = -P :=
  phi_sum F P

/-- Every nonzero seven-torsion point has one of three possible abscissas. -/
theorem seven_torsion_x_cube {x y : F} {h : (W F).Nonsingular x y}
    (hP : (7 : ℕ) • (.some x y h : Points F) = 0) : x ^ 3 + 1 = 0 := by
  have hTwo := double_eq_phi_squared F (.some x y h) hP
  have hx : x ≠ 0 := by
    intro hx
    subst x
    simp only [phi_app, phiFun_some, mul_zero, two_nsmul] at hTwo
    have hz : (.some 0 y h : Points F) = 0 :=
      add_right_cancel (hTwo.trans (zero_add _).symm)
    change Affine.Point.some 0 y h = Affine.Point.zero at hz
    cases hz
  simp only [phi_app, phiFun_some] at hTwo
  have hDouble := doubling_x F hTwo
  have he := (equation_iff F x y).mp h.1
  have hX : 9 * x ^ 3 = 24 * (x ^ 3 + 5) := by
    apply mul_left_cancel₀ hx
    rw [← he]
    linear_combination hDouble
  linear_combination -hX - (2 * x ^ 3 + 17) * seven_zero F

theorem seven_torsion_coordinates {x y : F} {h : (W F).Nonsingular x y}
    (hP : (7 : ℕ) • (.some x y h : Points F) = 0) :
    (x = 3 ∨ x = 5 ∨ x = 6) ∧ (y = 2 ∨ y = 5) := by
  have hx := seven_torsion_x_cube F hP
  have hy := (equation_iff F x y).mp h.1
  have hxf : (x - 3) * (x - 5) * (x - 6) = 0 := by
    linear_combination hx + (-2 * x ^ 2 + 9 * x - 13) * seven_zero F
  have hyf : (y - 2) * (y - 5) = 0 := by
    linear_combination hy + hx + (2 - y) * seven_zero F
  simpa only [mul_eq_zero, sub_eq_zero, or_assoc] using And.intro hxf hyf

end

end ManuscriptAudit.Paper5OrdinarySevenGeometry

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5OrdinarySevenGeometry.rotation_some,
      ``ManuscriptAudit.Paper5OrdinarySevenGeometry.rotation_sum,
      ``ManuscriptAudit.Paper5OrdinarySevenGeometry.seven_torsion_x_cube,
      ``ManuscriptAudit.Paper5OrdinarySevenGeometry.seven_torsion_coordinates] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
