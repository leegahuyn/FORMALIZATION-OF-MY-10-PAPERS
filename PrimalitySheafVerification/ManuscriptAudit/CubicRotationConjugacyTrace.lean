import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicRotationCyclicBasis
import PrimalitySheafVerification.ManuscriptAudit.CyclotomicConjugationTrace

/-! Every two-power torsion trace vanishes for a native map conjugating the cube rotation. -/

namespace ManuscriptAudit.CubicRotationConjugacyTrace

open FiniteFieldPointCount CubicThreeTorsionOrdinate CubicThreeTorsionCard
open CubicCubeRotation CubicRotationCyclicBasis
open TorsionFrobeniusModule TwoPowerTorsionTower CyclotomicConjugationTrace

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K] {A z : K}

/-- On the genuine positive torsion levels, conjugation by the cube root forces trace zero. -/
theorem trace_det_of_point_conjugacy (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0)
    (hz : z ^ 3 = 1) (hz₁ : z ≠ 1) (f : (Curve A).Point →+ (Curve A).Point)
    (hf : ∀ P : (Curve A).Point,
      let r := rotate z hz (shortCubic_discriminant_ne_zero h₂ h₃ hA)
      f (r P) = r (r (f P))) (n : ℕ) :
    let m := 2 ^ (n + 1)
    let F := mapLinear m f
    LinearMap.trace (ZMod m) (PowerTorsion (Curve A).Point (n + 1)) F = 0 ∧
      ∃ a c : ZMod m, LinearMap.det F = -(a ^ 2 - a * c + c ^ 2) := by
  let S := rotationLinear h₂ h₃ hA hz (n + 1)
  let F := mapLinear (2 ^ (n + 1)) f
  obtain ⟨B, hB⟩ := exists_rotation_basis h₂ h₃ hA hz hz₁ n
  have hc : S (S (S (B 0))) = B 0 := rotation_linear_cube h₂ h₃ hA hz (n + 1) (B 0)
  have hq : S (S (B 0)) = -B 0 - S (B 0) := rotation_linear_quad h₂ h₃ hA hz hz₁ (n + 1) (B 0)
  have he : F (S (B 0)) = S (S (F (B 0))) :=
    Subtype.ext (hf (B 0 : (Curve A).Point))
  change LinearMap.trace (ZMod (2 ^ (n + 1))) _ F = 0 ∧ _
  exact trace_det_of_cycle B S F hB hc (hq.trans (by rw [hB])) he

end
end ManuscriptAudit.CubicRotationConjugacyTrace

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicRotationConjugacyTrace.trace_det_of_point_conjugacy
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
