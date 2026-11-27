import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicOrdinatePreservingTwist
import PrimalitySheafVerification.ManuscriptAudit.CubicRotationCombination
import PrimalitySheafVerification.ManuscriptAudit.CubicTateRotationCoefficients

/-! Native ℤ₂ and ℤ₃ Frobenius coefficients on an ordinate-preserving actual twist. -/

namespace ManuscriptAudit.CubicOrdinatePreservingTate

open WeierstrassCurve FiniteFieldPointCount CubicTwoTorsion CubicThreeTorsionOrdinate
open CubicFrobeniusSexticTwists CubicOrdinatePreservingTwist CubicRotationCombination
open PowerTateModule

noncomputable section

set_option maxHeartbeats 800000

variable {E L : Type*} [Field E] [Fintype E] [Field L] [Algebra E L]
    [IsAlgClosed L] [DecidableEq L]

theorem trace_det (h₂ : (2 : L) ≠ 0) (h₃ : (3 : L) ≠ 0) (A B : E)
    (hA : A ≠ 0) (hB : B ≠ 0) {k : ℕ} (hq : Fintype.card E = 6 * k + 1)
    (hΔA : (shortCubic (0 : L) (algebraMap E L A)).Δ ≠ 0)
    (hΔB : (shortCubic (0 : L) (algebraMap E L B)).Δ ≠ 0)
    (z : L) (hz : z ^ 3 = 1) (hz₁ : z ≠ 1)
    (n : Fin 3) (hX : (algebraMap E L (parameter A B k)) ^ 2 = z ^ n.val)
    (hY : (algebraMap E L (parameter A B k)) ^ 3 = 1)
    (a b : ℤ)
    (hF : arithmeticFrobenius E L A =
      a • (1 : AddMonoid.End (Geometric E L A)) +
        b • (pointRotation hz hΔA : AddMonoid.End (Geometric E L A)))
    (l : ℕ) [Fact l.Prime] (hl : l = 2 ∨ l = 3) :
    let c := (rotatedCoefficients n a b).1
    let d := (rotatedCoefficients n a b).2
    LinearMap.trace ℤ_[l] (Tate l (Geometric E L B))
      (endMap l (arithmeticFrobenius E L B)) = ((2 * c - d : ℤ) : ℤ_[l]) ∧
    LinearMap.det (endMap l (arithmeticFrobenius E L B)) = ((c ^ 2 - c * d + d ^ 2 : ℤ) : ℤ_[l]) := by
  let r : AddMonoid.End (Geometric E L A) := pointRotation hz hΔA
  have h₀ : algebraMap E L A ≠ 0 := (map_ne_zero (algebraMap E L)).mpr hA
  have hr : r ^ 2 + r + (1 : AddMonoid.End (Geometric E L A)) = 0 := by
    apply AddMonoidHom.ext
    intro P
    change r (r P) + r P + P = 0
    exact CubicRotationQuadratic.rotate_sum_eq_zero h₂ h₃ h₀ hz hz₁ hΔA P
  let F := r ^ n.val * arithmeticFrobenius E L A
  let c := (rotatedCoefficients n a b).1
  let d := (rotatedCoefficients n a b).2
  have hRot : F = c • (1 : AddMonoid.End (Geometric E L A)) + d • r := by
    calc
      F = r ^ n.val * (a • (1 : AddMonoid.End (Geometric E L A)) + b • r) :=
        congrArg (fun t : AddMonoid.End (Geometric E L A) => r ^ n.val * t) hF
      _ = c • (1 : AddMonoid.End (Geometric E L A)) + d • r := rotation_pow_linear r hr n a b
  obtain ⟨ht, hd⟩ := CubicTateRotationCoefficients.trace_det h₂ h₃ h₀ hz hz₁ hΔA
    l hl F c d hRot
  obtain ⟨e, he⟩ := frobenius_conjugate_rotation (E := E) (L := L) (A := A) (B := B)
    (z := z) (n := n.val) hA hB hq hΔA hΔB hz hX hY
  let T := mapAddEquiv l e
  let G := endMap l (arithmeticFrobenius E L B)
  have h (v : Tate l (Geometric E L A)) : G (T v) = T (endMap l F v) := by
    apply PowerTateModule.ext l (Geometric E L B)
    intro j
    apply Subtype.ext
    exact he (evaluate l (Geometric E L A) j v : Geometric E L A)
  have hConj : T.conj (endMap l F) = G := by
    apply LinearMap.ext
    intro x
    change T (endMap l F (T.symm x)) = G x
    rw [← h, T.apply_symm_apply]
  change LinearMap.trace ℤ_[l] (Tate l (Geometric E L B)) G = ((2 * c - d : ℤ) : ℤ_[l]) ∧
    LinearMap.det G = ((c ^ 2 - c * d + d ^ 2 : ℤ) : ℤ_[l])
  rw [← hConj]
  refine ⟨(LinearMap.trace_conj' _ _).trans ht, ?_⟩
  have hMap : T.conj (endMap l F) = T.toLinearMap ∘ₗ (endMap l F) ∘ₗ T.symm.toLinearMap := by
    apply LinearMap.ext
    intro v
    rfl
  rw [hMap]
  exact (LinearMap.det_conj (endMap l F) T).trans hd

end
end ManuscriptAudit.CubicOrdinatePreservingTate

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.CubicOrdinatePreservingTate.trace_det
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
