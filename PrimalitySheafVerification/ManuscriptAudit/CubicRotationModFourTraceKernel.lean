import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicRotationModFourKernel
import PrimalitySheafVerification.ManuscriptAudit.CubicRotationModFourTraceModel

/-! Native trace alternatives for a norm-one operator in the cyclic rotation algebra. -/

namespace ManuscriptAudit.CubicRotationModFourTraceKernel

open Module CubicRotationModFourModel CubicRotationModFourKernel CubicRotationCentralizer

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module (ZMod 4) V]

/-- Trace, two-torsion fixed points, and cubic fixed counts in the norm-one case. -/
def TracePatterns (F : Module.End (ZMod 4) V) : Prop :=
  let t := LinearMap.trace (ZMod 4) V F
  (t = 2 ∧ ∀ x : V, (2 : ℕ) • x = 0 → F x = x) ∨
  (t = 1 ∧ (∀ x : V, (2 : ℕ) • x = 0 → F x = x → x = 0) ∧
    Nat.card {x : V // (F ^ 3) x = x} = 4) ∨
  (t = 3 ∧ (∀ x : V, (2 : ℕ) • x = 0 → F x = x → x = 0) ∧
    Nat.card {x : V // (F ^ 3) x = x} = 16)

theorem trace_fixed_patterns (B : Basis (Fin 2) (ZMod 4) V)
    (S F : Module.End (ZMod 4) V) (h₀ : S (B 0) = B 1) (h₁ : S (B 1) = -B 0 - B 1)
    (a b : ZMod 4) (hF : F = a • 1 + b • S) (hd : LinearMap.det F = 1) :
    TracePatterns F := by
  letI : Fact (1 < (4 : ℕ)) := ⟨by decide⟩
  let M := action a b
  let M₃ := fun v => M (M (M v))
  have hcoef : LinearMap.trace (ZMod 4) V F = 2 * a - b ∧
      LinearMap.det F = norm a b := by
    rw [hF]
    exact trace_det_of_form B S h₀ h₁ a b
  have ha (x : V) : coordinates B (F x) = M (coordinates B x) := by
    rw [hF]
    exact coordinates_action B S h₀ h₁ a b x
  have hc (x : V) : coordinates B ((F ^ 3) x) = M₃ (coordinates B x) := by
    change coordinates B (F (F (F x))) = _
    simp only [ha, M₃]
  have h2 (x : V) (hx : (2 : ℕ) • x = 0) : (2 : ℕ) • coordinates B x = 0 := by
    rw [← map_nsmul, hx, map_zero]
  have only_zero
      (hz : ∀ v : Coordinates, (2 : ℕ) • v = 0 → M v = v → v = 0)
      (x : V) (hx : (2 : ℕ) • x = 0) (hFx : F x = x) : x = 0 := by
    have hM : M (coordinates B x) = coordinates B x := (ha x).symm.trans
      (congrArg (coordinates B) hFx)
    exact (coordinates B).injective
      ((hz (coordinates B x) (h2 x hx) hM).trans (map_zero (coordinates B)).symm)
  have hmodel := CubicRotationModFourTraceModel.trace_fixed_patterns a b (hcoef.2.symm.trans hd)
  unfold TracePatterns
  dsimp only
  rw [hcoef.1, fixed_card (coordinates B).toEquiv _ M₃ hc]
  rcases hmodel with ⟨ht, hAll⟩ | ⟨ht, ht2, hCard⟩ | ⟨ht, ht2, hCard⟩
  · exact Or.inl ⟨ht, fun x hx =>
      (coordinates B).injective ((ha x).trans (hAll (coordinates B x) (h2 x hx)))⟩
  · exact Or.inr (Or.inl ⟨ht, only_zero ht2, hCard⟩)
  · exact Or.inr (Or.inr ⟨ht, only_zero ht2, hCard⟩)

end
end ManuscriptAudit.CubicRotationModFourTraceKernel

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicRotationModFourTraceKernel.trace_fixed_patterns
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
