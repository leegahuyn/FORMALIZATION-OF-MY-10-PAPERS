import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicRotationQuadratic
import PrimalitySheafVerification.ManuscriptAudit.CubicSplitTwoAdicForm
import PrimalitySheafVerification.ManuscriptAudit.CubicThreePowerTorsion
import PrimalitySheafVerification.ManuscriptAudit.PowerTateCoefficientUniqueness
import PrimalitySheafVerification.ManuscriptAudit.PowerTateEvaluationSurjective

/-! Native rotation coordinates for split Frobenius on the genuine three-adic Tate module. -/

namespace ManuscriptAudit.CubicSplitThreeAdicForm

open CubicThreeTorsionOrdinate CubicNonsplitThreeAdicTrace CubicSplitTwoPowerFrobenius
open CubicThreeFrobeniusSigns CubicTriplingSurjective CubicRotationCentralizer
open PowerTateModule PowerTorsionTower PowerTateLinearCombination
open PowerTateCoefficientReduction PowerTateCoefficientUniqueness PowerTateEvaluationSurjective
open TorsionFrobeniusModule

noncomputable section

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

variable (E L : Type*) [Field E] [Fintype E] [Field L] [Algebra E L] [IsAlgClosed L] [DecidableEq L]
variable {A : E} (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0) (hA : A ≠ 0)
variable {z : E} (hz : IsPrimitiveRoot z 3)

abbrev Level (A : E) (n : ℕ) := PowerTorsion 3 (GeometricPoints E L A) n

abbrev levelRotation (n : ℕ) : Module.End (ZMod (3 ^ n)) (Level E L A n) :=
  mapLinear (3 ^ n) (geometricRotation E L h₂ h₃ hA hz)

abbrev levelFrobenius (A : E) (n : ℕ) : Module.End (ZMod (3 ^ n)) (Level E L A n) :=
  mapLinear (3 ^ n) (arithmeticPointFrobenius E L A)

private theorem rotation_basis (n : ℕ) :
    ∃ B : Module.Basis (Fin 2) (ZMod (3 ^ (n + 1))) (Level E L A (n + 1)),
      levelRotation E L h₂ h₃ hA hz (n + 1) (B 0) = B 1 ∧
      levelRotation E L h₂ h₃ hA hz (n + 1) (B 1) = -B 0 - B 1 := by
  have h₂L : (2 : L) ≠ 0 := by simpa only [map_ofNat] using (map_ne_zero (algebraMap E L)).mpr h₂
  have h₃L : (3 : L) ≠ 0 := by simpa only [map_ofNat] using (map_ne_zero (algebraMap E L)).mpr h₃
  have hAL : (algebraMap E L A) ≠ 0 := (map_ne_zero (algebraMap E L)).mpr hA
  have hzL := hz.map_of_injective (algebraMap E L).injective
  have hz₁ := hzL.ne_one (by decide)
  obtain ⟨B, hB⟩ := CubicThreePowerTorsion.exists_cyclic_basis h₂L h₃L hAL hzL.pow_eq_one hz₁ n
  let S := levelRotation E L h₂ h₃ hA hz (n + 1)
  have h₀ : S (B 0) = B 1 := hB
  have hΔ := CubicThreeTorsionCard.shortCubic_discriminant_ne_zero h₂L h₃L hAL
  have hq := CubicRotationQuadratic.rotation_linear_quad (3 ^ (n + 1)) h₂L h₃L hAL
    hzL.pow_eq_one hz₁ hΔ (B 0)
  change S (S (B 0)) = -B 0 - S (B 0) at hq
  rw [h₀] at hq
  exact ⟨B, h₀, hq⟩

private theorem level_commutes (n : ℕ) :
    levelFrobenius E L A n * levelRotation E L h₂ h₃ hA hz n =
      levelRotation E L h₂ h₃ hA hz n * levelFrobenius E L A n := by
  apply LinearMap.ext
  intro P
  apply Subtype.ext
  exact congrArg (fun F : AddMonoid.End (GeometricPoints E L A) => F P.val)
    (geometric_commutes E L h₂ h₃ hA hz)

theorem level_form (n : ℕ) :
    ∃! ab : ZMod (3 ^ (n + 1)) × ZMod (3 ^ (n + 1)),
      levelFrobenius E L A (n + 1) = ab.1 • 1 + ab.2 • levelRotation E L h₂ h₃ hA hz (n + 1) := by
  obtain ⟨B, h₀, _⟩ := rotation_basis E L h₂ h₃ hA hz n
  exact exists_unique_coefficients B _ h₀ _ (level_commutes E L h₂ h₃ hA hz (n + 1))

theorem level_trace_det (n : ℕ) (a b : ZMod (3 ^ (n + 1)))
    (h : levelFrobenius E L A (n + 1) = a • 1 + b • levelRotation E L h₂ h₃ hA hz (n + 1)) :
    LinearMap.trace (ZMod (3 ^ (n + 1))) (Level E L A (n + 1))
        (levelFrobenius E L A (n + 1)) = 2 * a - b ∧
      LinearMap.det (levelFrobenius E L A (n + 1)) = a ^ 2 - a * b + b ^ 2 := by
  letI : NeZero (3 ^ (n + 1) : ℕ) := ⟨pow_ne_zero _ (by decide)⟩
  letI : Fact (1 < (3 ^ (n + 1) : ℕ)) := ⟨by
    rw [pow_succ]
    have : 0 < (3 : ℕ) ^ n := pow_pos (by decide) _
    omega⟩
  obtain ⟨B, h₀, h₁⟩ := rotation_basis E L h₂ h₃ hA hz n
  rw [h]
  exact trace_det_of_form B _ h₀ h₁ a b

theorem hasUniqueCoordinates :
    ∃! ab : ℤ_[3] × ℤ_[3],
      arithmeticTateFrobenius E L A = ab.1 • 1 + ab.2 • endMap 3 (geometricRotation E L h₂ h₃ hA hz) ∧
      LinearMap.trace ℤ_[3] (Tate 3 (GeometricPoints E L A)) (arithmeticTateFrobenius E L A) =
        2 * ab.1 - ab.2 ∧
      LinearMap.det (arithmeticTateFrobenius E L A) = ab.1 ^ 2 - ab.1 * ab.2 + ab.2 ^ 2 := by
  let G := GeometricPoints E L A
  let f := arithmeticPointFrobenius E L A
  let r := geometricRotation E L h₂ h₃ hA hz
  have h₂L : (2 : L) ≠ 0 := by simpa only [map_ofNat] using (map_ne_zero (algebraMap E L)).mpr h₂
  have h₃L : (3 : L) ≠ 0 := by simpa only [map_ofNat] using (map_ne_zero (algebraMap E L)).mpr h₃
  have hAL : (algebraMap E L A) ≠ 0 := (map_ne_zero (algebraMap E L)).mpr hA
  obtain ⟨B, _, _⟩ := rotation_basis E L h₂ h₃ hA hz 0
  have hDiv : Function.Surjective (fun P : G => (3 : ℕ) • P) :=
    affine_tripling_surjective h₂L h₃L hAL
  have hForm (n : ℕ) : ∃! ab, LevelForm 3 G f r (n + 1) ab :=
    level_form E L h₂ h₃ hA hz n
  have hEval := evaluate_surjective 3 G B hDiv
  obtain ⟨⟨a, b⟩, hEq, hUnique⟩ := exists_unique_adic_form 3 G f r hForm
    (transition_surjective 3 G hDiv) hEval
  have hLevel (n : ℕ) := level_form_of_adic 3 G f r (n + 1) (hEval (n + 1)) a b hEq
  refine ⟨(a, b), ⟨hEq, ?_, ?_⟩, fun cd hc => hUnique cd hc.1⟩
  · apply PadicInt.ext_of_toZModPow.mp
    intro n
    cases n with
    | zero =>
      letI : Subsingleton (ZMod (3 ^ 0)) := inferInstanceAs (Subsingleton (ZMod 1))
      exact Subsingleton.elim _ _
    | succ n =>
      have he := (trace_det_reduce 3 G B hDiv f (n + 1)).1
      have ht := (level_trace_det E L h₂ h₃ hA hz n _ _ (hLevel n)).1
      exact he.trans (ht.trans (by simp only [map_sub, map_mul, map_ofNat]))
  · apply PadicInt.ext_of_toZModPow.mp
    intro n
    cases n with
    | zero =>
      letI : Subsingleton (ZMod (3 ^ 0)) := inferInstanceAs (Subsingleton (ZMod 1))
      exact Subsingleton.elim _ _
    | succ n =>
      have he := (trace_det_reduce 3 G B hDiv f (n + 1)).2
      have hd := (level_trace_det E L h₂ h₃ hA hz n _ _ (hLevel n)).2
      exact he.trans (hd.trans (by simp only [map_add, map_sub, map_mul, map_pow]))

end
end ManuscriptAudit.CubicSplitThreeAdicForm

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicSplitThreeAdicForm.level_form,
      ``ManuscriptAudit.CubicSplitThreeAdicForm.level_trace_det,
      ``ManuscriptAudit.CubicSplitThreeAdicForm.hasUniqueCoordinates] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
