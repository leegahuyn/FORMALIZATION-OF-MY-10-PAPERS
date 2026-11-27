import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicEvenExtensionTwists
import PrimalitySheafVerification.ManuscriptAudit.CubicPointScaling

/-! In even extensions the actual nonsplit projective points have the unit-twist count. -/

namespace ManuscriptAudit.CubicEvenExtensionPointCounts

open WeierstrassCurve FiniteFieldPointCount CubicPointScaling
open CubicEvenExtensionTwists CubicThreeTorsionCard

noncomputable section

variable (F E : Type*) [Field F] [Fintype F] [DecidableEq F]
variable [Field E] [Fintype E] [DecidableEq E] [Algebra F E]

def projective_points_equiv (hF : ringChar F ≠ 2) (hE : ringChar E ≠ 2)
    (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0)
    (hq : Fintype.card F % 3 = 2) (hEven : Even (Module.finrank F E)) {a : F} (ha : a ≠ 0) :
    (shortCubic (0 : E) (algebraMap F E a)).toProjective.Point ≃
      (shortCubic (0 : E) 1).toProjective.Point := by
  let u := (sixth_root_in_even_extension F E hF hE hq hEven ha).choose
  have hu := (sixth_root_in_even_extension F E hF hE hq hEven ha).choose_spec
  have hA : algebraMap F E a ≠ 0 := (map_ne_zero (algebraMap F E)).mpr ha
  let e := scaleEquiv hu.1 (show u ^ (6 : ℕ) * (1 : E) = algebraMap F E a by simpa using hu.2)
    (shortCubic_discriminant_ne_zero h₂ h₃ one_ne_zero)
    (shortCubic_discriminant_ne_zero h₂ h₃ hA)
  let eA := Projective.Point.toAffineAddEquiv (W := (shortCubic (0 : E) (algebraMap F E a)).toProjective)
  let eOne := Projective.Point.toAffineAddEquiv (W := (shortCubic (0 : E) 1).toProjective)
  exact eA.toEquiv.trans (e.toEquiv.symm.trans eOne.toEquiv.symm)

theorem projective_card_eq (hF : ringChar F ≠ 2) (hE : ringChar E ≠ 2)
    (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0)
    (hq : Fintype.card F % 3 = 2) (hEven : Even (Module.finrank F E)) {a : F} (ha : a ≠ 0) :
    Nat.card (shortCubic (0 : E) (algebraMap F E a)).toProjective.Point =
      Nat.card (shortCubic (0 : E) 1).toProjective.Point :=
  Nat.card_congr (projective_points_equiv F E hF hE h₂ h₃ hq hEven ha)

end
end ManuscriptAudit.CubicEvenExtensionPointCounts

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicEvenExtensionPointCounts.projective_card_eq
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
