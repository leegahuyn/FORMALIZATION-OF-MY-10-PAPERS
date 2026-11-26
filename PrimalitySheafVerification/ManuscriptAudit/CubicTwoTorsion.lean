import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.FiniteFieldPointCount

/-! The actual two-torsion points on the nonsingular short Weierstrass models. -/

namespace ManuscriptAudit.CubicTwoTorsion

open FiniteFieldPointCount
open WeierstrassCurve

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K]

abbrev CubicAffine (c A : K) := (shortCubic c A).toProjective.toAffine

abbrev TwoTorsion (c A : K) := {P : (CubicAffine c A).Point // 2 • P = 0}

abbrev CubicRoots (c A : K) := {x : K // x ^ 3 - c * x + A = 0}

private theorem cubic_nonsingular_iff {c A : K}
    (hΔ : (shortCubic c A).Δ ≠ 0) (x y : K) :
    (CubicAffine c A).Nonsingular x y ↔ y ^ 2 = x ^ 3 - c * x + A := by
  rw [← Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ, Affine.equation_iff]
  simp [CubicAffine, shortCubic, sub_eq_add_neg, neg_mul]

private theorem neg_eq_self_iff_two_nsmul {G : Type*} [AddCommGroup G] (P : G) :
    -P = P ↔ 2 • P = 0 := by
  rw [two_nsmul]
  constructor
  · intro h
    simpa only [h] using neg_add_cancel P
  · intro h
    calc
      -P = -P + 0 := (add_zero _).symm
      _ = -P + (P + P) := by rw [h]
      _ = P := by rw [← add_assoc, neg_add_cancel, zero_add]

theorem two_nsmul_affine_some_iff {c A x y : K}
    (h2 : (2 : K) ≠ 0) (h : (CubicAffine c A).Nonsingular x y) :
    (2 • (Affine.Point.some x y h : (CubicAffine c A).Point) = 0) ↔ y = 0 := by
  rw [← neg_eq_self_iff_two_nsmul, Affine.Point.neg_some]
  have hy : (CubicAffine c A).negY x y = -y := by simp [Affine.negY, shortCubic]
  constructor
  · intro he
    let ordinate : (CubicAffine c A).Point → K := fun
      | .zero => 0
      | .some _ y _ => y
    have ey : (CubicAffine c A).negY x y = y := congrArg ordinate he
    rw [hy] at ey
    have hz : (2 : K) * y = 0 := by
      calc
        _ = y + y := by ring
        _ = (-y) + y := congrArg (fun z => z + y) ey.symm
        _ = _ := neg_add_cancel _
    exact (mul_eq_zero.mp hz).resolve_left h2
  · rintro rfl
    simp [Affine.negY, shortCubic]

/-- The identity and the points with zero ordinate are all actual two-torsion points. -/
def affineTwoTorsionEquiv {c A : K} (hΔ : (shortCubic c A).Δ ≠ 0)
    (h2 : (2 : K) ≠ 0) : TwoTorsion c A ≃ Option (CubicRoots c A) where
  toFun
    | ⟨.zero, _⟩ => none
    | ⟨.some x y h, hP⟩ => by
      have hy := (two_nsmul_affine_some_iff h2 h).mp hP
      have he := (cubic_nonsingular_iff hΔ x y).mp h
      rw [hy, zero_pow (by decide : (2 : ℕ) ≠ 0)] at he
      exact some ⟨x, he.symm⟩
  invFun
    | none => ⟨0, nsmul_zero _⟩
    | some x => by
      have h : (CubicAffine c A).Nonsingular x 0 :=
        (cubic_nonsingular_iff hΔ x 0).mpr (by simp [x.property])
      exact ⟨.some x 0 h, (two_nsmul_affine_some_iff h2 h).mpr rfl⟩
  left_inv := by
    rintro ⟨P, hP⟩
    cases P with
    | zero => rfl
    | some x y h =>
      have hy := (two_nsmul_affine_some_iff h2 h).mp hP
      subst y
      rfl
  right_inv := by
    rintro (_ | x)
    · rfl
    · rfl

def projectiveTwoTorsionEquiv {c A : K} (hΔ : (shortCubic c A).Δ ≠ 0)
    (h2 : (2 : K) ≠ 0) :
    {P : (shortCubic c A).toProjective.Point // 2 • P = 0} ≃ Option (CubicRoots c A) := by
  let e := Projective.Point.toAffineAddEquiv (W := (shortCubic c A).toProjective)
  let er : {P : (shortCubic c A).toProjective.Point // 2 • P = 0} ≃ TwoTorsion c A :=
    { toFun := fun P => ⟨e P, by rw [← map_nsmul, P.property, map_zero]⟩
      invFun := fun Q => ⟨e.symm Q, by rw [← map_nsmul, Q.property, map_zero]⟩
      left_inv := fun P => Subtype.ext (e.symm_apply_apply P)
      right_inv := fun Q => Subtype.ext (e.apply_symm_apply Q) }
  exact er.trans (affineTwoTorsionEquiv hΔ h2)

end
end ManuscriptAudit.CubicTwoTorsion

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicTwoTorsion.two_nsmul_affine_some_iff,
      ``ManuscriptAudit.CubicTwoTorsion.affineTwoTorsionEquiv,
      ``ManuscriptAudit.CubicTwoTorsion.projectiveTwoTorsionEquiv] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
