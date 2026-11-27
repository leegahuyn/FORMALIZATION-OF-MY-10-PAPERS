import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicOrdinatePreservingTwist

/-! The actual sextic twist acts by a cubic rotation and an ordinate sign. -/

namespace ManuscriptAudit.CubicSignedTwistRotation

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate
open CubicPointScaling CubicFrobeniusSexticTwists CubicOrdinatePreservingTwist

noncomputable section

variable {L : Type*} [Field L] [DecidableEq L] {A z v : L}

private theorem negY_eq (x y : L) : (Curve A).negY x y = -y := by
  simp [Curve, CubicAffine, shortCubic, Affine.negY]

/-- Both ordinate signs are realized by multiplication of the point-group map by ±1. -/
theorem scale_eq_signed_pow (hz : z ^ 3 = 1)
    (hΔ : (shortCubic (0 : L) A).Δ ≠ 0) (hv : v ≠ 0) (hV : v ^ 6 * A = A)
    (n : ℕ) (hx : v ^ 2 = z ^ n)
    (ε : ℤ) (hε : ε = 1 ∨ ε = -1) (hy : v ^ 3 = (ε : L)) :
    scale hv hV hΔ = ε • (pointRotation hz hΔ ^ n) := by
  rcases hε with hε | hε
  · subst ε
    rw [one_zsmul]
    exact scale_eq_rotation_pow hz hΔ hv hV n hx (by simpa only [Int.cast_one] using hy)
  · subst ε
    rw [neg_one_zsmul]
    apply AddMonoidHom.ext
    intro P
    cases P with
    | zero =>
        change scale hv hV hΔ (0 : (Curve A).Point) = -(pointRotation hz hΔ ^ n) 0
        rw [map_zero, map_zero, neg_zero]
    | some x y h =>
        obtain ⟨h', he⟩ := rotation_pow_some hz hΔ n h
        change scale hv hV hΔ (Affine.Point.some x y h) =
          -((pointRotation hz hΔ ^ n) (Affine.Point.some x y h))
        rw [he, scale_some, Affine.Point.neg_some, Affine.Point.some.injEq]
        exact ⟨by rw [hx], by rw [hy, Int.cast_neg, Int.cast_one, neg_one_mul, negY_eq]⟩

variable (E : Type*) (L) [Field E] [Fintype E] [Algebra E L] [IsAlgClosed L]

/-- The native Frobenius of the target twist is conjugate to the signed rotation of the reference one. -/
theorem frobenius_conjugate_signed_pow {A B : E} (hA : A ≠ 0) (hB : B ≠ 0)
    {k : ℕ} (hq : Fintype.card E = 6 * k + 1)
    (hΔA : (shortCubic (0 : L) (algebraMap E L A)).Δ ≠ 0)
    (hΔB : (shortCubic (0 : L) (algebraMap E L B)).Δ ≠ 0)
    {z : L} (hz : z ^ 3 = 1) (n : ℕ)
    (hx : (algebraMap E L (parameter A B k)) ^ 2 = z ^ n)
    (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hy : (algebraMap E L (parameter A B k)) ^ 3 = (ε : L)) :
    ∃ e : Geometric E L A ≃+ Geometric E L B, ∀ P,
      arithmeticFrobenius E L B (e P) =
        e ((ε • (pointRotation hz hΔA ^ n * arithmeticFrobenius E L A)) P) := by
  obtain ⟨hv, hV, e, he⟩ := CubicFrobeniusSexticTwists.exists_conjugacy E L hA hB hq hΔA hΔB
  have hScale := scale_eq_signed_pow hz hΔA hv hV n hx ε hε hy
  rw [hScale] at he
  refine ⟨e, fun P => (he P).trans ?_⟩
  apply congrArg e
  rcases hε with hε | hε <;> simp only [hε, one_zsmul, neg_one_zsmul] <;> rfl

end
end ManuscriptAudit.CubicSignedTwistRotation

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicSignedTwistRotation.scale_eq_signed_pow,
      ``ManuscriptAudit.CubicSignedTwistRotation.frobenius_conjugate_signed_pow] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
