import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicSplitTwoPowerFrobenius
import PrimalitySheafVerification.ManuscriptAudit.CubicTwoPowerTorsionBasis
import PrimalitySheafVerification.ManuscriptAudit.PowerTateCoefficientReduction
import PrimalitySheafVerification.ManuscriptAudit.PowerTateLinearCombination

/-! The split Frobenius has genuine 2-adic coordinates in its rotation algebra. -/

namespace ManuscriptAudit.CubicSplitTwoAdicForm

open CubicThreeTorsionOrdinate CubicNonsplitThreeAdicTrace CubicSplitTwoPowerFrobenius
open CubicDoublingSurjective CubicThreeFrobeniusSigns
open PowerTateLinearCombination PowerTateModule PowerTorsionTower PowerTateCoefficientReduction

noncomputable section

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

variable (E L : Type*) [Field E] [Fintype E] [Field L] [Algebra E L] [IsAlgClosed L] [DecidableEq L]
variable {A : E} (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0) (hA : A ≠ 0)

abbrev ActualTate := Tate 2 (GeometricPoints E L A)

abbrev ActualFrobenius : Module.End ℤ_[2] (ActualTate E L (A := A)) :=
  endMap 2 (arithmeticPointFrobenius E L A)

def HasRotationForm {z : E} (hz : IsPrimitiveRoot z 3) : Prop :=
  ∃ a b : ℤ_[2],
    ActualFrobenius E L (A := A) = a • 1 + b • endMap 2 (geometricRotation E L h₂ h₃ hA hz) ∧
    LinearMap.trace ℤ_[2] (ActualTate E L (A := A)) (ActualFrobenius E L (A := A)) = 2 * a - b ∧
    LinearMap.det (ActualFrobenius E L (A := A)) = a ^ 2 - a * b + b ^ 2

/-- The actual Tate action has compatible rotation coordinates, trace and norm. -/
theorem hasRotationForm {z : E} (hz : IsPrimitiveRoot z 3) :
    HasRotationForm E L h₂ h₃ hA hz := by
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
  obtain ⟨a, b, hAdic, hLevel⟩ := exists_adic_form 2 G f r hForm (transition_surjective 2 G hDiv)
  refine ⟨a, b, hAdic, ?_, ?_⟩
  · apply PadicInt.ext_of_toZModPow.mp
    intro n
    cases n with
    | zero =>
      letI : Subsingleton (ZMod (2 ^ 0)) := inferInstanceAs (Subsingleton (ZMod 1))
      exact Subsingleton.elim _ _
    | succ n =>
      have he := (trace_det_reduce 2 G B hDiv f (n + 1)).1
      have ht := (level_trace_det E L h₂ h₃ hA hz n _ _ (hLevel n)).1
      exact he.trans (ht.trans (by simp only [map_sub, map_mul, map_ofNat]))
  · apply PadicInt.ext_of_toZModPow.mp
    intro n
    cases n with
    | zero =>
      letI : Subsingleton (ZMod (2 ^ 0)) := inferInstanceAs (Subsingleton (ZMod 1))
      exact Subsingleton.elim _ _
    | succ n =>
      have he := (trace_det_reduce 2 G B hDiv f (n + 1)).2
      have hd := (level_trace_det E L h₂ h₃ hA hz n _ _ (hLevel n)).2
      exact he.trans (hd.trans (by simp only [map_add, map_sub, map_mul, map_pow]))

theorem hasRotationForm_of_card_mod_three (hq : Fintype.card E % 3 = 1) :
    ∃ z : E, ∃ hz : IsPrimitiveRoot z 3, HasRotationForm E L h₂ h₃ hA hz := by
  obtain ⟨z, hz⟩ := finite_exists_primitive_cube_root hq
  exact ⟨z, hz, hasRotationForm E L h₂ h₃ hA hz⟩

end
end ManuscriptAudit.CubicSplitTwoAdicForm

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicSplitTwoAdicForm.hasRotationForm,
      ``ManuscriptAudit.CubicSplitTwoAdicForm.hasRotationForm_of_card_mod_three] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
