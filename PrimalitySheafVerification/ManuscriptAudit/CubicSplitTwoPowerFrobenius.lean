import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicNonsplitThreeAdicTrace
import PrimalitySheafVerification.ManuscriptAudit.CubicRotationCentralizer
import PrimalitySheafVerification.ManuscriptAudit.CubicRotationCyclicBasis

/-! The split Frobenius lies in the actual rotation algebra at every two-power level. -/

namespace ManuscriptAudit.CubicSplitTwoPowerFrobenius

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate CubicThreeTorsionCard
open CubicCubeRotation CubicNonsplitThreeAdicTrace CubicRotationCentralizer
open TorsionFrobeniusModule TwoPowerTorsionTower

noncomputable section

variable (E L : Type*) [Field E] [Fintype E] [Field L] [Algebra E L] [DecidableEq L]

private theorem two_ne (h : (2 : E) ≠ 0) : (2 : L) ≠ 0 := by
  simpa only [map_ofNat] using (map_ne_zero (algebraMap E L)).mpr h

private theorem three_ne (h : (3 : E) ≠ 0) : (3 : L) ≠ 0 := by
  simpa only [map_ofNat] using (map_ne_zero (algebraMap E L)).mpr h

variable {A : E} (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0) (hA : A ≠ 0)
variable {z : E} (hz : IsPrimitiveRoot z 3)

private theorem discriminant_ne :
    (shortCubic (0 : L) (algebraMap E L A)).Δ ≠ 0 :=
  shortCubic_discriminant_ne_zero (two_ne E L h₂) (three_ne E L h₃)
    ((map_ne_zero (algebraMap E L)).mpr hA)

private theorem primitive : IsPrimitiveRoot (algebraMap E L z) 3 :=
  hz.map_of_injective (algebraMap E L).injective

def geometricRotation : AddMonoid.End (GeometricPoints E L A) :=
  rotate (algebraMap E L z) (primitive E L hz).pow_eq_one (discriminant_ne E L h₂ h₃ hA)

theorem geometric_commutes [IsAlgClosed L] :
    arithmeticPointFrobenius E L A * geometricRotation E L h₂ h₃ hA hz =
      geometricRotation E L h₂ h₃ hA hz * arithmeticPointFrobenius E L A := by
  apply AddMonoidHom.ext
  intro P
  let g := FiniteField.frobeniusAlgHom E L
  change arithmeticPointFrobenius E L A (geometricRotation E L h₂ h₃ hA hz P) =
    geometricRotation E L h₂ h₃ hA hz (arithmeticPointFrobenius E L A P)
  exact CubicNonsplitFrobeniusTrace.pointMapAt_intertwines_rotation E L (Curve A)
    (CubicNonsplitFrobeniusTrace.centered_baseChange E L A) g (g.commutes z)
    (primitive E L hz).pow_eq_one (primitive E L hz).pow_eq_one
    (discriminant_ne E L h₂ h₃ hA) P

abbrev Level (A : E) (n : ℕ) := PowerTorsion (GeometricPoints E L A) n

def levelRotation (n : ℕ) : Module.End (ZMod (2 ^ n)) (Level E L A n) :=
  mapLinear (2 ^ n) (geometricRotation E L h₂ h₃ hA hz)

variable [IsAlgClosed L]

def levelFrobenius (A : E) (n : ℕ) : Module.End (ZMod (2 ^ n)) (Level E L A n) :=
  mapLinear (2 ^ n) (arithmeticPointFrobenius E L A)

theorem level_commutes (n : ℕ) :
    levelFrobenius E L A n * levelRotation E L h₂ h₃ hA hz n =
      levelRotation E L h₂ h₃ hA hz n * levelFrobenius E L A n := by
  apply LinearMap.ext
  intro P
  apply Subtype.ext
  exact congrArg (fun f : AddMonoid.End (GeometricPoints E L A) => f P.val)
    (geometric_commutes E L h₂ h₃ hA hz)

/-- Actual Frobenius has unique rotation coordinates on every positive two-power torsion level. -/
theorem level_form (n : ℕ) :
    ∃! ab : ZMod (2 ^ (n + 1)) × ZMod (2 ^ (n + 1)),
      levelFrobenius E L A (n + 1) = ab.1 • 1 + ab.2 • levelRotation E L h₂ h₃ hA hz (n + 1) := by
  letI : NeZero (2 ^ (n + 1) : ℕ) := ⟨pow_ne_zero _ (by decide)⟩
  letI : Fact (1 < (2 ^ (n + 1) : ℕ)) := ⟨by
    rw [pow_succ]
    have : 0 < (2 : ℕ) ^ n := pow_pos (by decide) _
    omega⟩
  let S := levelRotation E L h₂ h₃ hA hz (n + 1)
  let F := levelFrobenius E L A (n + 1)
  obtain ⟨B, hB⟩ := CubicRotationCyclicBasis.exists_rotation_basis
    (two_ne E L h₂) (three_ne E L h₃) ((map_ne_zero (algebraMap E L)).mpr hA)
    (primitive E L hz).pow_eq_one ((primitive E L hz).ne_one (by decide)) n
  exact exists_unique_coefficients B S hB F (level_commutes E L h₂ h₃ hA hz (n + 1))

theorem level_trace_det (n : ℕ) (a b : ZMod (2 ^ (n + 1)))
    (h : levelFrobenius E L A (n + 1) = a • 1 + b • levelRotation E L h₂ h₃ hA hz (n + 1)) :
    LinearMap.trace (ZMod (2 ^ (n + 1))) (Level E L A (n + 1))
        (levelFrobenius E L A (n + 1)) = 2 * a - b ∧
      LinearMap.det (levelFrobenius E L A (n + 1)) = a ^ 2 - a * b + b ^ 2 := by
  letI : NeZero (2 ^ (n + 1) : ℕ) := ⟨pow_ne_zero _ (by decide)⟩
  letI : Fact (1 < (2 ^ (n + 1) : ℕ)) := ⟨by
    rw [pow_succ]
    have : 0 < (2 : ℕ) ^ n := pow_pos (by decide) _
    omega⟩
  let S := levelRotation E L h₂ h₃ hA hz (n + 1)
  obtain ⟨B, hB⟩ := CubicRotationCyclicBasis.exists_rotation_basis
    (two_ne E L h₂) (three_ne E L h₃) ((map_ne_zero (algebraMap E L)).mpr hA)
    (primitive E L hz).pow_eq_one ((primitive E L hz).ne_one (by decide)) n
  have h₀ : S (B 0) = B 1 := hB
  have hSq : S (S (B 0)) = -B 0 - S (B 0) :=
    CubicRotationCyclicBasis.rotation_linear_quad
      (two_ne E L h₂) (three_ne E L h₃) ((map_ne_zero (algebraMap E L)).mpr hA)
      (primitive E L hz).pow_eq_one ((primitive E L hz).ne_one (by decide)) _ (B 0)
  rw [h₀] at hSq
  rw [h]
  exact trace_det_of_form B S h₀ hSq a b

end
end ManuscriptAudit.CubicSplitTwoPowerFrobenius

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicSplitTwoPowerFrobenius.geometric_commutes,
      ``ManuscriptAudit.CubicSplitTwoPowerFrobenius.level_commutes,
      ``ManuscriptAudit.CubicSplitTwoPowerFrobenius.level_form,
      ``ManuscriptAudit.CubicSplitTwoPowerFrobenius.level_trace_det] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
