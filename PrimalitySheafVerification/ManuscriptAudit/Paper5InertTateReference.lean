import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicCertifiedInertTate
import PrimalitySheafVerification.ManuscriptAudit.Paper5CertifiedSplitTwistTate

/-! Any checked split-prime reference certificate gives full inert-prime Tate arithmetic. -/

namespace ManuscriptAudit.Paper5InertTateReference

open FiniteFieldPointCount CubicThreeTorsionOrdinate CubicThreeTorsionCard
open CubicSplitExtensionTraceRecurrence CubicFrobeniusSexticTwists
open Paper5SplitTwistCertificate Paper5CertifiedSplitTwistTate CubicCertifiedInertTate
open CubicSexticTwistCoefficientFormula CubicSignedTwistTate CubicRotationCombination

noncomputable section

variable {p : ℕ} [Fact p.Prime]
variable (c : Certificate p) (L : Type*) [Field L] [Algebra (ZMod p) L] [IsAlgClosed L] [DecidableEq L]

/-- The certified native order-three coefficient identity on A=1 is a literal integral reference. -/
def reference (hF : IsNativeReference c L) : IntegralReference p L := by
  obtain ⟨h₂p, h₃p⟩ := Paper5NonsplitFrobeniusModFour.small_char p (ZMod p) c.lower
  let i := algebraMap (ZMod p) L
  have h₂ : (2 : L) ≠ 0 := by simpa only [map_ofNat] using (map_ne_zero i).mpr h₂p
  have h₃ : (3 : L) ≠ 0 := by simpa only [map_ofNat] using (map_ne_zero i).mpr h₃p
  have hA : i (1 : ZMod p) ≠ 0 := (map_ne_zero i).mpr one_ne_zero
  have hΔ := shortCubic_discriminant_ne_zero h₂ h₃ hA
  have hz := c.primitive.map_of_injective i.injective
  let r : AddMonoid.End (Geometric (ZMod p) L 1) :=
    CubicCubeRotation.rotate (i c.z) hz.pow_eq_one hΔ
  have hQuad : r ^ 2 + r + 1 = 0 := by
    apply AddMonoidHom.ext
    intro P
    change r (r P) + r P + P = 0
    exact CubicRotationQuadratic.rotate_sum_eq_zero h₂ h₃ hA hz.pow_eq_one
      (hz.ne_one (by decide)) hΔ P
  have hTrace : signedTrace (1 : ZMod p) = 2 * c.a - c.b := by
    rw [← prediction_eq_count c (one_ne_zero : (1 : ZMod p) ≠ 0)]
    simp [prediction, predictedTrace, rotationIndex, ordinateSign, signedCoefficients, rotatedCoefficients]
  exact
    { goodPrime := c.lower
      splitPrime := by have := c.card; omega
      A := 1
      nonzeroA := one_ne_zero
      rotation := r
      quadratic := hQuad
      a := c.a
      b := c.b
      native := hF
      trace := hTrace
      norm := c.norm }

end
end ManuscriptAudit.Paper5InertTateReference

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper5InertTateReference.reference
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
