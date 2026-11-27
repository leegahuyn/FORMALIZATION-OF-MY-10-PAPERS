import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicFrobeniusSexticTwists
import PrimalitySheafVerification.ManuscriptAudit.CubicCubeRotation
import PrimalitySheafVerification.ManuscriptAudit.TorsionFrobeniusModule

/-! A sextic twist with trivial ordinate correction acts by a pure cubic rotation on the source. -/

namespace ManuscriptAudit.CubicOrdinatePreservingTwist

open WeierstrassCurve FiniteFieldPointCount CubicTwoTorsion CubicThreeTorsionOrdinate
open CubicPointScaling CubicFrobeniusSexticTwists

noncomputable section

variable {L : Type*} [Field L] [DecidableEq L] {A z : L}

abbrev pointRotation (hz : z ^ 3 = 1) (hΔ : (shortCubic (0 : L) A).Δ ≠ 0) :
    AddMonoid.End (Curve A).Point :=
  CubicCubeRotation.rotate z hz hΔ

private theorem rotation_pow_some (hz : z ^ 3 = 1)
    (hΔ : (shortCubic (0 : L) A).Δ ≠ 0) (n : ℕ) {x y : L}
    (h : (Curve A).Nonsingular x y) :
    ∃ h' : (Curve A).Nonsingular (z ^ n * x) y,
      (pointRotation hz hΔ ^ n) (Affine.Point.some x y h) =
        Affine.Point.some (z ^ n * x) y h' := by
  induction n with
  | zero =>
    refine ⟨by simpa using h, ?_⟩
    rw [pow_zero]
    change Affine.Point.some x y h = _
    simp only [Affine.Point.some.injEq, pow_zero, one_mul, and_self]
  | succ n ih =>
    obtain ⟨h', he⟩ := ih
    have h'' : (Curve A).Nonsingular (z * (z ^ n * x)) y := by
      apply (nonsingular_iff hΔ _ _).mpr
      rw [mul_pow, hz, one_mul]
      exact (nonsingular_iff hΔ _ _).mp h'
    have hx : z * (z ^ n * x) = z ^ (n + 1) * x := by
      rw [pow_succ', mul_assoc]
    refine ⟨by simpa only [hx] using h'', ?_⟩
    rw [pow_succ']
    change pointRotation hz hΔ
      ((pointRotation hz hΔ ^ n) (Affine.Point.some x y h)) = _
    rw [he]
    change CubicCubeRotation.rotate z hz hΔ (Affine.Point.some (z ^ n * x) y h') = _
    rw [CubicCubeRotation.rotate_some, Affine.Point.some.injEq]
    exact ⟨hx, rfl⟩

theorem scale_eq_rotation_pow (hz : z ^ 3 = 1)
    (hΔ : (shortCubic (0 : L) A).Δ ≠ 0) {v : L} (hv : v ≠ 0)
    (hV : v ^ 6 * A = A) (n : ℕ) (hx : v ^ 2 = z ^ n) (hy : v ^ 3 = 1) :
    scale hv hV hΔ = pointRotation hz hΔ ^ n := by
  apply AddMonoidHom.ext
  intro P
  cases P with
  | zero =>
    change scale hv hV hΔ (0 : (Curve A).Point) = (pointRotation hz hΔ ^ n) 0
    have hleft : scale hv hV hΔ (0 : (Curve A).Point) = 0 :=
      (scale hv hV hΔ).map_zero
    have hright : (pointRotation hz hΔ ^ n) (0 : (Curve A).Point) = 0 :=
      ((pointRotation hz hΔ ^ n : AddMonoid.End (Curve A).Point) :
        (Curve A).Point →+ (Curve A).Point).map_zero
    exact hleft.trans hright.symm
  | some x y h =>
    obtain ⟨h', he⟩ := rotation_pow_some hz hΔ n h
    calc
      scale hv hV hΔ (Affine.Point.some x y h) =
          Affine.Point.some (v ^ 2 * x) (v ^ 3 * y) _ :=
        CubicPointScaling.scale_some hv hV hΔ h
      _ = Affine.Point.some (z ^ n * x) y h' := by
        rw [Affine.Point.some.injEq, hx, hy, one_mul]
        exact ⟨rfl, rfl⟩
      _ = (pointRotation hz hΔ ^ n) (Affine.Point.some x y h) := he.symm

variable (E : Type*) (L) [Field E] [Fintype E] [Algebra E L] [IsAlgClosed L]

theorem frobenius_conjugate_rotation (A B : E) (hA : A ≠ 0) (hB : B ≠ 0)
    {k : ℕ} (hq : Fintype.card E = 6 * k + 1)
    (hΔA : (shortCubic (0 : L) (algebraMap E L A)).Δ ≠ 0)
    (hΔB : (shortCubic (0 : L) (algebraMap E L B)).Δ ≠ 0) (z : L) (hz : z ^ 3 = 1)
    (n : ℕ) (hx : (algebraMap E L (parameter A B k)) ^ 2 = z ^ n)
    (hy : (algebraMap E L (parameter A B k)) ^ 3 = 1) :
    ∃ e : Geometric E L A ≃+ Geometric E L B, ∀ P,
      arithmeticFrobenius E L B (e P) =
        e ((pointRotation hz hΔA ^ n * arithmeticFrobenius E L A) P) := by
  obtain ⟨hv, hV, e, he⟩ := CubicFrobeniusSexticTwists.exists_conjugacy
    E L hA hB hq hΔA hΔB
  refine ⟨e, fun P => ?_⟩
  have hScale := scale_eq_rotation_pow hz hΔA hv hV n hx hy
  rw [hScale] at he
  exact he P

end
end ManuscriptAudit.CubicOrdinatePreservingTwist

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicOrdinatePreservingTwist.scale_eq_rotation_pow,
      ``ManuscriptAudit.CubicOrdinatePreservingTwist.frobenius_conjugate_rotation] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
