import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicSplitTwoAdicForm
import PrimalitySheafVerification.ManuscriptAudit.PowerTateCoefficientUniqueness
import PrimalitySheafVerification.ManuscriptAudit.PowerTateEvaluationSurjective

/-! The two native split 2-adic Frobenius coordinates are unique. -/

namespace ManuscriptAudit.CubicSplitTwoAdicUniqueForm

open CubicThreeTorsionOrdinate CubicNonsplitThreeAdicTrace CubicSplitTwoPowerFrobenius
open CubicDoublingSurjective CubicThreeFrobeniusSigns CubicSplitTwoAdicForm
open PowerTateModule PowerTorsionTower PowerTateLinearCombination
open PowerTateCoefficientUniqueness PowerTateEvaluationSurjective

noncomputable section

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

variable (E L : Type*) [Field E] [Fintype E] [Field L] [Algebra E L] [IsAlgClosed L] [DecidableEq L]
variable {A : E} (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0) (hA : A ≠ 0)

theorem hasUniqueCoordinates {z : E} (hz : IsPrimitiveRoot z 3) :
    ∃! ab : ℤ_[2] × ℤ_[2],
      ActualFrobenius E L (A := A) = ab.1 • 1 + ab.2 • endMap 2 (geometricRotation E L h₂ h₃ hA hz) ∧
      LinearMap.trace ℤ_[2] (ActualTate E L (A := A)) (ActualFrobenius E L (A := A)) = 2 * ab.1 - ab.2 ∧
      LinearMap.det (ActualFrobenius E L (A := A)) = ab.1 ^ 2 - ab.1 * ab.2 + ab.2 ^ 2 := by
  let G := GeometricPoints E L A
  let f := arithmeticPointFrobenius E L A
  let r := geometricRotation E L h₂ h₃ hA hz
  have h₂L : (2 : L) ≠ 0 := by simpa only [map_ofNat] using (map_ne_zero (algebraMap E L)).mpr h₂
  have h₃L : (3 : L) ≠ 0 := by simpa only [map_ofNat] using (map_ne_zero (algebraMap E L)).mpr h₃
  have hAL : (algebraMap E L A) ≠ 0 := (map_ne_zero (algebraMap E L)).mpr hA
  let B := CubicTwoPowerTorsionBasis.affineBasis h₂L h₃L hAL 1
  have hDiv : Function.Surjective (fun P : G => (2 : ℕ) • P) :=
    affine_doubling_surjective h₂L h₃L hAL
  have hForm (n : ℕ) : ∃! ab, LevelForm 2 G f r (n + 1) ab :=
    level_form E L h₂ h₃ hA hz n
  obtain ⟨ab, _, hUniq⟩ := exists_unique_adic_form 2 G f r hForm
    (transition_surjective 2 G hDiv) (evaluate_surjective 2 G B hDiv)
  obtain ⟨a, b, he, ht, hd⟩ := hasRotationForm E L h₂ h₃ hA hz
  refine ⟨(a, b), ⟨he, ht, hd⟩, ?_⟩
  intro cd hc
  exact (hUniq cd hc.1).trans (hUniq (a, b) he).symm

end
end ManuscriptAudit.CubicSplitTwoAdicUniqueForm

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicSplitTwoAdicUniqueForm.hasUniqueCoordinates
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
