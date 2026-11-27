import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicSupersingularTwistTateFormula

/-! Actual prime-adic Frobenius over even-degree fields in supersingular characteristic. -/

namespace ManuscriptAudit.CubicSupersingularTwistTate

open Module WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionCard
open CubicNonsplitThreeAdicTrace PowerTateModule CubicSupersingularUnitFrobenius
open CubicSupersingularTwistFrobenius CubicSexticRotation

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (L : Type*) [Field L] [DecidableEq L] [Algebra (ZMod p) L] [IsAlgClosed L]
variable [Algebra.IsAlgebraic (ZMod p) L]
variable (l : ℕ) [Fact l.Prime]
variable (E : Type*) [Field E] [Fintype E] [Algebra (ZMod p) E] [Algebra E L]

/-- Every nonzero centered twist over a degree-2m field in this characteristic has
determinant q and actual trace in {2, -2, 1, -1} times (-p)^m. -/
theorem trace_det_even (hp : 5 ≤ p) (hp₃ : p % 3 = 2) (hlp : l ≠ p)
    {m : ℕ} (hm : finrank (ZMod p) E = 2 * m) {A : E} (hA : A ≠ 0) :
    let T := endMap l (arithmeticPointFrobenius E L A)
    ∃ t : ℤ, (t = 2 ∨ t = -2 ∨ t = 1 ∨ t = -1) ∧
      LinearMap.trace ℤ_[l] (Tate l (GeometricPoints E L A)) T =
        (Int.cast (t * (-(p : ℤ)) ^ m) : ℤ_[l]) ∧
      LinearMap.det T = (Fintype.card E : ℤ_[l]) := by
  obtain ⟨h₂p, h₃p⟩ := Paper5NonsplitFrobeniusModFour.small_char p (ZMod p) hp
  have h₂ : (2 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap (ZMod p) L)).mpr h₂p
  have h₃ : (3 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap (ZMod p) L)).mpr h₃p
  have hΔ := shortCubic_discriminant_ne_zero h₂ h₃ (one_ne_zero : (1 : L) ≠ 0)
  have hΔA := shortCubic_discriminant_ne_zero h₂ h₃ ((map_ne_zero (algebraMap E L)).mpr hA)
  obtain ⟨v, hv, e, he⟩ := exists_twist_conjugacy L E hA hΔ hΔA
  let t := twistSign L v * (if v ^ 2 = 1 then (2 : ℤ) else -1)
  obtain ⟨ht, hd⟩ := CubicSupersingularTwistTateFormula.trace_det_for_twist
    p L l E hp hp₃ hlp hm h₂ h₃ hΔ hv e he
  refine ⟨t, ?_, ht, hd⟩
  by_cases h : v ^ 2 = 1 <;>
    rcases twistSign_cases L v with h₁ | h₁ <;> simp [t, h, h₁]

end
end ManuscriptAudit.CubicSupersingularTwistTate

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicSupersingularTwistTate.trace_det_even
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
