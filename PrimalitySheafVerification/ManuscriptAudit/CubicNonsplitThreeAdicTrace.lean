import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicNonsplitFrobeniusTrace
import PrimalitySheafVerification.ManuscriptAudit.CubicRotationQuadratic
import PrimalitySheafVerification.ManuscriptAudit.CubicThreeAdicTate
import PrimalitySheafVerification.ManuscriptAudit.CyclotomicTateTrace

/-! The full native 3-adic Frobenius trace in the nonsplit centered cubic family. -/

namespace ManuscriptAudit.CubicNonsplitThreeAdicTrace

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate CubicThreeTorsionCard
open CubicCubeRotation CubicRotationQuadratic CubicThreeFrobeniusSigns CubicThreePointCounts
open CubicNonsplitFrobeniusTrace PowerTateModule

noncomputable section

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

variable (E : Type*) [Field E] [Fintype E]
variable (L : Type*) [Field L] [Algebra E L] [IsAlgClosed L] [DecidableEq L]

abbrev GeometricPoints (A : E) := (Curve (algebraMap E L A)).Point

def arithmeticPointFrobenius (A : E) : AddMonoid.End (GeometricPoints E L A) :=
  pointMapAt E L (Curve A) (Curve (algebraMap E L A))
    (centered_baseChange E L A) (FiniteField.frobeniusAlgHom E L)

def arithmeticTateFrobenius (A : E) :
    Module.End ℤ_[3] (Tate 3 (GeometricPoints E L A)) :=
  endMap 3 (arithmeticPointFrobenius E L A)

/-- The native prime-adic trace vanishes for every prime-adic limit in the nonsplit case. -/
theorem actual_prime_adic_trace_zero (l : ℕ) [Fact l.Prime] {A : E}
    (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0) (hA : A ≠ 0)
    (hq : Fintype.card E % 3 = 2) :
    LinearMap.trace ℤ_[l] (Tate l (GeometricPoints E L A))
      (endMap l (arithmeticPointFrobenius E L A)) = 0 := by
  let a := algebraMap E L A
  have h₂L : (2 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap E L)).mpr h₂
  have h₃L : (3 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap E L)).mpr h₃
  have ha : a ≠ 0 := (map_ne_zero (algebraMap E L)).mpr hA
  let hΔ := shortCubic_discriminant_ne_zero h₂L h₃L ha
  obtain ⟨z, hz, hz₁⟩ := exists_nontrivial_cubeRoot h₃L
  let r : AddMonoid.End ((Curve a).Point) := rotate z hz hΔ
  let f : AddMonoid.End ((Curve a).Point) := arithmeticPointFrobenius E L A
  have hCube : r ^ 3 = 1 := by
    apply AddMonoidHom.ext
    intro P
    change r (r (r P)) = P
    exact rotate_cube hz hΔ P
  have hQuad : r ^ 2 + r + 1 = 0 := by
    apply AddMonoidHom.ext
    intro P
    change r (r P) + r P + P = 0
    exact rotate_sum_eq_zero h₂L h₃L ha hz hz₁ hΔ P
  have hg : FiniteField.frobeniusAlgHom E L z = z ^ 2 := by
    change z ^ Fintype.card E = z ^ 2
    rw [pow_cube_reduce z _ hz, hq]
  have hConj : f * r = r ^ 2 * f := by
    apply AddMonoidHom.ext
    intro P
    change f (r P) = r (r (f P))
    exact pointMapAt_conjugates_rotation E L (Curve A) (centered_baseChange E L A)
      (FiniteField.frobeniusAlgHom E L) hg hz hΔ P
  exact CyclotomicTateTrace.trace_eq_zero l r f hCube hQuad hConj

theorem actual_trace_zero {A : E}
    (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0) (hA : A ≠ 0)
    (hq : Fintype.card E % 3 = 2) :
    LinearMap.trace ℤ_[3] (Tate 3 (GeometricPoints E L A)) (arithmeticTateFrobenius E L A) = 0 :=
  actual_prime_adic_trace_zero E L 3 h₂ h₃ hA hq

theorem actual_trace_eq_signed_point_count {A : E} [DecidableEq E]
    (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0) (hA : A ≠ 0)
    (hq : Fintype.card E % 3 = 2) :
    LinearMap.trace ℤ_[3] (Tate 3 (GeometricPoints E L A)) (arithmeticTateFrobenius E L A) =
      (((Fintype.card E : ℤ) + 1 -
        (Nat.card (shortCubic (0 : E) A).toProjective.Point : ℤ)) : ℤ_[3]) := by
  rw [actual_trace_zero E L h₂ h₃ hA hq, projective_count_residue_two A h₂ h₃ hA hq]
  simp [Nat.cast_add]

end
end ManuscriptAudit.CubicNonsplitThreeAdicTrace

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicNonsplitThreeAdicTrace.arithmeticTateFrobenius,
      ``ManuscriptAudit.CubicNonsplitThreeAdicTrace.actual_prime_adic_trace_zero,
      ``ManuscriptAudit.CubicNonsplitThreeAdicTrace.actual_trace_zero,
      ``ManuscriptAudit.CubicNonsplitThreeAdicTrace.actual_trace_eq_signed_point_count] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
